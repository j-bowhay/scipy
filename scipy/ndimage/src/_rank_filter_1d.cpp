// Copyright (c) 2011 ashelly.myopenid.com under
// <http://www.opensource.org/licenses/mit-license>
// Modified in 2024 by Gideon Genadi Kogan

#include "Python.h"
#include "numpy/arrayobject.h"

#include <stdio.h>
#include <stdlib.h>
#include <memory>
#include <stdexcept>


struct Mediator {
  std::unique_ptr<int[]> pos;  // index into `heap` for each value
  std::unique_ptr<int[]> heap_storage; // storage for heap array
  int* heap; // max/rank/min heap holding indexes into `data`
  int N;   // allocated size
  int idx;   // position in circular queue
  int minCt; // count of items in min heap
  int maxCt; // count of items in max heap
};

typedef enum {
  NEAREST = 0,
  WRAP = 1,
  REFLECT = 2,
  MIRROR = 3,
  CONSTANT = 4,
} Mode;

/*--- Helper Functions ---*/

// returns 1 if heap[i] < heap[j]
template <typename T>
inline int mmless(T* data, Mediator* m, int i, int j) {
  return (data[m->heap[i]] < data[m->heap[j]]);
}

// swaps items i&j in heap, maintains indexes
int mmexchange(Mediator* m, int i, int j) {
  int t = m->heap[i];
  m->heap[i] = m->heap[j];
  m->heap[j] = t;
  m->pos[m->heap[i]] = i;
  m->pos[m->heap[j]] = j;
  return 1;
}

// swaps items i & j if i < j;  returns true if swapped
template <typename T> inline int mmCmpExch(T* data, Mediator* m, int i, int j) {
  return (mmless(data, m, i, j) && mmexchange(m, i, j));
}

// maintains minheap property for all items below i.
template <typename T> void minSortDown(T* data, Mediator* m, int i) {
  for (i *= 2; i <= m->minCt; i *= 2) {
    if (i < m->minCt && mmless(data, m, i + 1, i)) {
      ++i;
    }
    if (!mmCmpExch(data, m, i, i / 2)) {
      break;
    }
  }
}

// maintains maxheap property for all items below i. (negative indexes)
template <typename T> void maxSortDown(T* data, Mediator* m, int i) {
  for (i *= 2; i >= -m->maxCt; i *= 2) {
    if (i > -m->maxCt && mmless(data, m, i, i - 1)) {
      --i;
    }
    if (!mmCmpExch(data, m, i / 2, i)) {
      break;
    }
  }
}

// maintains minheap property for all items above i, including the rank
// returns true if rank changed
template <typename T> inline int minSortUp(T* data, Mediator* m, int i) {
  while (i > 0 && mmCmpExch(data, m, i, i / 2))
    i /= 2;
  return (i == 0);
}

// maintains maxheap property for all items above i, including rank
// returns true if rank changed
template <typename T> inline int maxSortUp(T* data, Mediator* m, int i) {
  while (i < 0 && mmCmpExch(data, m, i / 2, i))
    i /= 2;
  return (i == 0);
}

/*--- Public Interface ---*/

// creates new Mediator: to calculate `nItems` running rank.
Mediator* MediatorNew(int nItems, int rank) {
  try {
    auto m = std::make_unique<Mediator>();
    m->pos = std::make_unique<int[]>(nItems);
    m->heap_storage = std::make_unique<int[]>(nItems);
    m->heap = m->heap_storage.get() + rank; // points to rank
    m->N = nItems;
    m->idx = 0;
    m->minCt = nItems - rank - 1;
    m->maxCt = rank;
    
    for (int i = 0; i < nItems; i++) {
      m->pos[i] = i - rank;
      m->heap[m->pos[i]] = i;
    }
    
    return m.release();
  } catch (const std::bad_alloc& e) {
    PyErr_SetString(PyExc_MemoryError, "Failed to allocate memory for Mediator");
    return nullptr;
  }
}

// Inserts item, maintains rank in O(lg nItems)
template <typename T>
void MediatorInsert(T* data, Mediator* m, T v) {
  int p = m->pos[m->idx];
  T old = data[m->idx];
  data[m->idx] = v;
  m->idx++;
  if (m->idx == m->N) {
    m->idx = 0;
  }

  if (p > 0) { // new item is in minHeap
    if (v > old) {
      minSortDown(data, m, p);
      return;
    }
    if (minSortUp(data, m, p) && mmCmpExch(data, m, 0, -1)) {
      maxSortDown(data, m, -1);
    }
  }
  else if (p < 0) { // new item is in maxheap
    if (v < old) {
      maxSortDown(data, m, p);
      return;
    }
    if (maxSortUp(data, m, p) && mmCmpExch(data, m, 1, 0)) {
      minSortDown(data, m, 1);
    }
  }
  else { // new item is at rank
    if (maxSortUp(data, m, -1)) {
      maxSortDown(data, m, -1);
    }
    if (minSortUp(data, m, 1)) {
      minSortDown(data, m, 1);
    }
  }
}

template <typename T>
void _rank_filter(T* in_arr, int rank, int arr_len, int win_len, T* out_arr,
         int mode, T cval, int origin) {
  std::unique_ptr<Mediator, void(*)(Mediator*)> m(nullptr, [](Mediator* m) {
    if (m) {
      // Smart pointers will clean up automatically
      m->heap = nullptr; // Reset this before deletion since it points into heap_storage
      delete m;
    }
  });
  
  std::unique_ptr<T[]> data;
  
  try {
    m.reset(MediatorNew(win_len, rank));
    if (!m) {
      throw std::runtime_error("Failed to create Mediator");
    }
    
    data = std::make_unique<T[]>(win_len);
    
    int i, arr_len_thresh, lim = (win_len - 1) / 2 - origin;
    int lim2 = arr_len - lim;

    switch (mode) {
      case REFLECT:
        for (i = win_len - lim - 1; i > -1; i--) {
          MediatorInsert(data.get(), m.get(), in_arr[i]);
        }
        break;
      case CONSTANT:
        for (i = win_len - lim; i > 0; i--) {
          MediatorInsert(data.get(), m.get(), cval);
        }
        break;
      case NEAREST:
        for (i = win_len - lim; i > 0; i--) {
          MediatorInsert(data.get(), m.get(), in_arr[0]);
        }
        break;
      case MIRROR:
        for (i = win_len - lim; i > 0; i--) {
          MediatorInsert(data.get(), m.get(), in_arr[i]);
        }
        break;
      case WRAP:
        for (i = arr_len - lim - 1 - 2 * origin; i < arr_len; i++) {
          MediatorInsert(data.get(), m.get(), in_arr[i]);
        }
        break;
    }

    for (i = 0; i < lim; i++) {
      MediatorInsert(data.get(), m.get(), in_arr[i]);
    }
    for (i = lim; i < arr_len; i++) {
      MediatorInsert(data.get(), m.get(), in_arr[i]);
      out_arr[i - lim] = data[m->heap[0]];
    }
    
    switch (mode) {
      case REFLECT:
        arr_len_thresh = arr_len - 1;
        for (i = 0; i < lim; i++) {
          MediatorInsert(data.get(), m.get(), in_arr[arr_len_thresh - i]);
          out_arr[lim2 + i] = data[m->heap[0]];
        }
        break;
      case CONSTANT:
        for (i = 0; i < lim; i++) {
          MediatorInsert(data.get(), m.get(), cval);
          out_arr[lim2 + i] = data[m->heap[0]];
        }
        break;
      case NEAREST:
        arr_len_thresh = arr_len - 1;
        for (i = 0; i < lim; i++) {
          MediatorInsert(data.get(), m.get(), in_arr[arr_len_thresh]);
          out_arr[lim2 + i] = data[m->heap[0]];
        }
        break;
      case MIRROR:
        arr_len_thresh = arr_len - 2;
        for (i = 0; i < lim + 1; i++) {
          MediatorInsert(data.get(), m.get(), in_arr[arr_len_thresh - i]);
          out_arr[lim2 + i] = data[m->heap[0]];
        }
        break;
      case WRAP:
        for (i = 0; i < win_len; i++) {
          MediatorInsert(data.get(), m.get(), in_arr[i]);
          out_arr[lim2 + i] = data[m->heap[0]];
        }
        break;
    }
    
  } catch (const std::exception& e) {
    PyErr_SetString(PyExc_RuntimeError, e.what());
    return;
  }
}

// Python wrapper for rank_filter
static PyObject* rank_filter(PyObject* self, PyObject* args) {
  PyObject *in_arr_obj, *out_arr_obj, *cval_obj;
  int rank, arr_len, win_len, mode, origin, type;
  
  if (!PyArg_ParseTuple(args, "OiiOiOi", &in_arr_obj, &rank, &win_len,
             &out_arr_obj, &mode, &cval_obj, &origin)) {
    return NULL;
  }
  
  // Use RAII for NumPy arrays
  PyArrayObject* in_arr = (PyArrayObject*)PyArray_FROM_OTF(
    in_arr_obj, NPY_NOTYPE, NPY_ARRAY_IN_ARRAY);
  if (!in_arr) {
    return NULL;
  }
  
  struct ArrayGuard {
    PyArrayObject* arr;
    ArrayGuard(PyArrayObject* a) : arr(a) {}
    ~ArrayGuard() { if (arr) Py_DECREF(arr); }
  } in_guard(in_arr);
  
  PyArrayObject* out_arr = (PyArrayObject*)PyArray_FROM_OTF(
    out_arr_obj, NPY_NOTYPE, NPY_ARRAY_INOUT_ARRAY2);
  if (!out_arr) {
    return NULL;
  }
  ArrayGuard out_guard(out_arr);
  
  arr_len = PyArray_SIZE(in_arr);
  type = PyArray_TYPE(in_arr);

  try {
    switch (type) {
      case NPY_FLOAT: {
        float* c_in_arr = (float*)PyArray_DATA(in_arr);
        float* c_out_arr = (float*)PyArray_DATA(out_arr);
        float cval = (float)PyFloat_AsDouble(cval_obj);
        _rank_filter(c_in_arr, rank, arr_len, win_len, c_out_arr, mode, cval,
               origin);
        break;
      }
      case NPY_DOUBLE: {
        double* c_in_arr = (double*)PyArray_DATA(in_arr);
        double* c_out_arr = (double*)PyArray_DATA(out_arr);
        double cval = PyFloat_AsDouble(cval_obj);
        _rank_filter(c_in_arr, rank, arr_len, win_len, c_out_arr, mode, cval,
               origin);
        break;
      }
      case NPY_INT64: {
        int64_t* c_in_arr = (int64_t*)PyArray_DATA(in_arr);
        int64_t* c_out_arr = (int64_t*)PyArray_DATA(out_arr);
        int64_t cval = PyLong_AsLongLong(cval_obj);
        _rank_filter(c_in_arr, rank, arr_len, win_len, c_out_arr, mode, cval,
               origin);
        break;
      }
      default:
        PyErr_SetString(PyExc_TypeError, "Unsupported array type");
        return NULL;
    }
  } catch (const std::exception& e) {
    PyErr_SetString(PyExc_RuntimeError, e.what());
    return NULL;
  }
  
  Py_RETURN_NONE;
}

// define the module methods
static PyMethodDef myMethods[] = {
  {"rank_filter", rank_filter, METH_VARARGS, "1D rank filter"},
  {NULL, NULL, 0, NULL}
};

// define the module
static struct PyModuleDef _rank_filter_1d = {
  PyModuleDef_HEAD_INIT,
  "_rank_filter_1d",
  "1D rank filter module",
  -1,
  myMethods
};

// init the module
PyMODINIT_FUNC PyInit__rank_filter_1d(void) {
  import_array();
  return PyModule_Create(&_rank_filter_1d);
}

