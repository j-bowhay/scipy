#include <math.h>
#include <complex.h>
#include "_amos.h"

int acai(
    double complex z,
    double fnu,
    int kode,
    int mr,
    int n,
    double complex *y,
    double rl,
    double tol,
    double elim,
    double alim
) {
    double complex csgn, cspn, c1, c2, zn, cy[2];
    double arg, ascle, az, cpn, dfnu, fmr, sgn, spn, yy;
    int inu, iuf, nn, nw;
    double pi = 3.14159265358979324;
    int nz = 0;
    zn = -z;
    az = cabs(z);
    nn = n;
    dfnu = fnu + (n-1);
    if (az > 2.) {
        if (az*az*0.25 > dfnu+1.0) {
            goto L10;
        }
    }
    //
    // POWER SERIES FOR THE I FUNCTION
    //
    seri(zn, fnu, kode, nn, y, tol, elim, alim);
    goto L40;
L10:
    if (az >= rl) {
        //
        // ASYMPTOTIC EXPANSION FOR LARGE Z FOR THE I FUNCTION
        //
        nw = asyi(zn, fnu, kode, nn, y, rl, tol, elim, alim);
        if (nw < 0) {
            nz = -1;
            if (nw == -2) { nz = -2; }
            return nz;
        }
    } else {
        //
        // MILLER ALGORITHM NORMALIZED BY THE SERIES FOR THE I FUNCTION
        //
        nw = mlri(zn, fnu, kode, nn, y, tol);
        if (nw < 0) {
            nz = -1;
            if (nw == -2) { nz = -2; }
            return nz;
        }
    }
L40:
//
// ANALYTIC CONTINUATION TO THE LEFT HALF PLANE FOR THE K FUNCTION
//
    nw = bknu(zn, fnu, kode, 1, &cy[0], tol, elim, alim);
    if (nw != 0) {
        nz = -1;
        if (nw == -2) { nz = -2; }
        return nz;
    }
    fmr = mr;
    sgn = (fmr < 0.0 ? pi : -pi);
    csgn = CMPLX(0.0, sgn);
    if (kode != 1) {
        yy = -cimag(zn);
        cpn = cos(yy);
        spn = sin(yy);
        csgn *= CMPLX(cpn, spn);
    }
    //
    // CALCULATE CSPN=EXP(FNU*PI*I) TO MINIMIZE LOSSES OF SIGNIFICANCE
    // WHEN FNU IS LARGE
    //
    inu = (int)fnu;
    arg = (fnu - inu)*sgn;
    cpn = cos(arg);
    spn = sin(arg);
    cspn = CMPLX(cpn, spn);
    if (inu % 2 == 1) { cspn = -cspn; }
    c1 = cy[0];
    c2 = y[0];
    if (kode != 1) {
        iuf = 0;
        ascle = 1e3 * d1mach[0] / tol;
        nw = s1s2(zn, &c1, &c2, ascle, alim, &iuf);
        nz += nw;
    }
    y[0] = cspn*c1 + csgn*c2;
    return nz;
}


double complex airy(
    double complex z,
    int id,
    int kode,
    int *nz,
    int *ierr
) {
    double complex ai, csq, cy[1], s1, s2, trm1, trm2, zta, z3;
    double aa, ad, ak, alim, atrm, az, az3, bk, ck, dig, dk, d1, d2,\
           elim, fid, fnu, rl, r1m5, sfac, tol, zi, zr, bb, alaz;
    int iflag, k, k1, k2, mr, nn;
    double tth = 2. / 3.;
    double c1 = 0.35502805388781723926;  /* 1/(Gamma(2/3) * 3**(2/3)) */
    double c2 = 0.25881940379280679841;  /* 1/(Gamma(1/3) * 3**(1/3)) */
    double coef = 0.18377629847393068317;  /* 1 / (sqrt(3) * PI) */

    *ierr = 0;
    *nz = 0;
    ai = 0.;
    if ((id < 0) || (id > 1)) { *ierr = 1; }
    if ((kode < 1) || (kode > 2)) { *ierr = 1; }
    if (*ierr != 0) return 0.;
    az = cabs(z);
    tol = d1mach[3];
    fid = id;

    if (az <= 1.0) {
        //
        // POWER SERIES FOR ABS(Z) <= 1.
        //
        s1 = 1.0;
        s2 = 1.0;
        if (az < tol) {
            aa = 1e3*d1mach[0];
            s1 = 0.;
            if (id != 1) {
                if (az > aa) { s1 = c2 * z; }
                ai = c1 - s1;
                return ai;
            }
            ai = -c2;
            aa = sqrt(aa);
            if (az > aa) { s1 = z * z * 0.5; }
            ai += s1 * c1;
            return ai;
        }
        aa = az*az;
        if (aa >= tol/az) {
            trm1 = 1.0;
            trm2 = 1.0;
            atrm = 1.0;
            z3 = z*z*z;
            az3 = az * aa;
            ak = 2.0 + fid;
            bk = 3.0 - fid - fid;
            ck = 4.0 - fid;
            dk = 3.0 + fid + fid;
            d1 = ak * dk;
            d2 = bk * ck;
            ad = (d1 > d2 ? d2 : d1);
            ak = 24.0 + 9.0*fid;
            bk = 30.0 - 9.0*fid;
            for (int k = 1; k < 26; k++)
            {
                trm1 *= z3/d1;
                s1 += trm1;
                trm2 *= z3/d2;
                s2 += trm2;
                atrm *= az3 / ad;
                d1 += ak;
                d2 += bk;
                ad = (d1 > d2 ? d2 : d1);
                if (atrm < tol*ad) { break; }
                ak += 18.0;
                bk += 18.0;
            }
        }
        if (id != 1) {
            ai = s1*c1 - z*s2*c2;
            if (kode == 1) { return ai; }
            zta = z*csqrt(z)*tth;
            ai *= cexp(zta);
            return ai;
        }
        ai = -s2*c2;
        if (az > tol) { ai += z*z*s1*c1/(1. + fid); }
        if (kode == 1) { return ai; }
        zta = z*csqrt(z)*tth;
        return ai*cexp(zta);
    }
    //
    // CASE FOR ABS(Z) > 1.0
    //
    fnu = (1.0 + fid) / 3.0;
    //
    // SET PARAMETERS RELATED TO MACHINE CONSTANTS.
    // TOL IS THE APPROXIMATE UNIT ROUNDOFF LIMITED TO 1.0E-18.
    // ELIM IS THE APPROXIMATE EXPONENTIAL OVER- AND UNDERFLOW LIMIT.
    // EXP(-ELIM) < EXP(-ALIM)=EXP(-ELIM)/TOL    AND
    // EXP(ELIM) > EXP(ALIM)=EXP(ELIM)*TOL       ARE INTERVALS NEAR
    // UNDERFLOW AND OVERFLOW LIMITS WHERE SCALED ARITHMETIC IS DONE.
    // RL IS THE LOWER BOUNDARY OF THE ASYMPTOTIC EXPANSION FOR LARGE Z.
    // DIG = NUMBER OF BASE 10 DIGITS IN TOL = 10**(-DIG).
    //
    k1 = i1mach[14];
    k2 = i1mach[15];
    r1m5 = d1mach[4];
    k = (abs(k1) > abs(k2) ? abs(k2) : abs(k1) );
    elim = 2.303 * (k*r1m5 - 3.0);
    k1 = i1mach[13] - 1;
    aa = r1m5*k1;
    dig = (aa > 18.0 ? 18.0 : aa);
    aa *= 2.303;
    alim = elim + (-aa > -41.45 ? -aa : -41.45);
    rl = 1.2*dig + 3.0;
    alaz = log(az);
    // 
    // TEST FOR RANGE
    // 
    aa = 0.5 / tol;
    bb = i1mach[8] * 0.5;
    aa = (aa > bb ? bb : aa);
    aa = pow(aa, tth);
    if (az > aa) {
        *ierr = 4;
        *nz = 0;
        return 0.;
    }
    aa = sqrt(aa);
    if (az > aa) { *ierr = 3; }
    csq = csqrt(z);
    zta = z * csq * tth;
    //
    // RE(ZTA) <= 0 WHEN RE(Z) < 0, ESPECIALLY WHEN IM(Z) IS SMALL
    // 
    iflag = 0;
    sfac = 1.0;
    zi = cimag(z);
    zr = creal(z);
    ak = cimag(zta);
    if (zr < 0.0) {
        bk = creal(zta);
        ck = -fabs(bk);
        zta = CMPLX(ck, ak);
    }
    if ((zi == 0.0) && (zr <= 0.0)) {
        zta = CMPLX(0.0, ak);
    }
    aa = creal(zta);
    if ((aa < 0.0) || (zr <= 0.0)) {
        if (kode != 2) {
            //
            // OVERFLOW TEST
            //
            if (aa <= -alim) {
                aa = -aa + 0.25*alaz;
                iflag = 1;
                sfac = tol;
                if (aa > elim) {
                    /* 270 */
                    *nz = 0;
                    *ierr = 2;
                    return ai;
                }
            }
        }
        //
        // CBKNU AND CACAI RETURN EXP(ZTA)*K(FNU,ZTA) ON KODE=2
        //
        mr = 1;
        if (zi < 0.0) { mr = -1; }
        nn = acai(zta, fnu, kode, mr, 1, &cy[0], rl, tol, elim, alim);
        if (nn < 0) {
            if (nn == -1) {
                *nz = 1;
                return 0.;
            } else {
                *nz = 0;
                *ierr = 5;
                return 0.;
            }
        }
        *nz += nn;
    } else {
        if (kode != 2) {
            //
            // UNDERFLOW TEST
            // 
            if (aa >= alim) {
                aa = -aa - 0.25 * alaz;
                iflag = 2;
                sfac = 1.0 / tol;
                if (aa < -elim) {
                    *nz = 1;
                    return 0.;
                }
            }
        }
        *nz = bknu(zta, fnu, kode, 1, &cy[0], tol, elim, alim);
    }
    s1 = cy[0]*coef;
    
    if (iflag == 0) {
        if (id != 1) {
            return csq *s1;
        }
        return (-z*s1);
    }
    s1 *= sfac;
    if (id != 1) {
        s1 *= csq;
        return (s1/sfac);
    }
    s1 *= -z;
    return (s1/sfac);
}


int asyi(
    double complex z,
    double fnu,
    int kode,
    int n,
    double complex *y,
    double rl,
    double tol,
    double elim,
    double alim
) {
    double complex ak1, ck, cs1, cs2, cz, dk, ez, p1, rz, s2;
    double aa, acz, aez, ak, arg, arm, atol, az, bb, bk, dfnu;
    double dnu2, fdn, rtr1, s, sgn, sqk, x, yy;
    int ib, il, inu, j, jl, k, koded, m, nn;
    double pi = 3.14159265358979324;
    double rpi = 0.159154943091895336; /* (1 / pi) */
    int nz = 0;
    az = cabs(z);
    x = creal(z);
    arm = 1e3*d1mach[0];
    rtr1 = sqrt(arm);
    il = (2 <= n ? 2 : n);
    dfnu = fnu + (n - il);
    // OVERFLOW TEST
    ak1 = sqrt(rpi / z);
    cz = z;
    if (kode == 2) { cz = z - x; }
    acz = creal(cz);
    if (fabs(acz) <= elim) {
        dnu2 = dfnu + dfnu;
        koded = 1;
        if (!((fabs(acz) > alim) && (n > 2))) {
            koded = 0;
            ak1 *= cexp(cz);
        }
        fdn = 0.;
        if (dnu2 > rtr1) { fdn = dnu2 * dnu2; }
        ez = z * 8.;
        // WHEN Z IS IMAGINARY, THE ERROR TEST MUST BE MADE
        // RELATIVE TO THE FIRST RECIPROCAL POWER SINCE THIS
        // IS THE LEADING TERM OF THE EXPANSION FOR THE
        // IMAGINARY PART.
        aez = 8. * az;
        s = tol / aez;
        jl = rl + rl + 2;
        yy = cimag(z);
        p1 = 0.;
        if (yy != 0.) {
            inu = (int)fnu;
            arg = (fnu - inu) * pi;
            inu += n - il;
            ak = -sin(arg);
            bk = cos(arg);
            if (yy < 0.) { bk = -bk; }
            p1 = ak + bk*I;
            if (inu % 2 == 1) { p1 = -p1; }
        }
        for (int k = 1; k < (il+1); k++)
        {
            sqk = fdn - 1.;
            atol = s*fabs(sqk);
            sgn = 1.;
            cs1 = 1.;
            cs2 = 1.;
            ck = 1.;
            ak = 0.;
            aa = 1.;
            bb = aez;
            dk = ez;
            j = 1;
            for (int j = 1; j < (jl+1); j++)
            {
                ck *= sqk / dk;
                cs2 += ck;
                sgn = -sgn;
                cs1 += ck*sgn;
                dk += ez;
                aa *= fabs(sqk) / bb;
                bb += aez;
                ak += 8.;
                sqk -= ak;
                if (aa <= atol) { break; }
            }
            if ((j == jl) && (aa > atol)) { return -2; }

            /* 20 */
            s2 = cs1;
            if (x + x < elim) { s2 += p1*cs2*cexp(-z-z); }
            fdn += 8. * dfnu + 4.;
            p1 = -p1;
            m = n - il + k;
            y[m - 1] = s2 * ak1;
        }
        if (n <= 2) { return nz; }
        nn = n;
        k = nn - 2;
        ak = k;
        rz = 2. / z;
        ib = 3;
        for (int i = ib; i < (nn+1); i++)
        {
            y[i-1] = (ak + fnu)*rz*y[k] + y[k+1];
            ak -= 1.;
            k -=1;
        }
        if (koded == 0) { return nz; }
        ck = cexp(cz);
        for (int i = 0; i < (nn + 1); i++) { y[i] *= ck; }
    }
    return -1;
}


int bknu(
    double complex z,
    double fnu,
    int kode,
    int n,
    double complex *y,
    double tol,
    double elim,
    double alim
) {
    double complex cch, ck, coef, crsc, cs, cscl, csh, cz,\
                   f, fmu, p, pt, p1, p2, q, rz, smu, st, s1, s2, zd;
    double aa, ak, ascle, a1, a2, bb, bk, caz, dnu, dnu2, etest, fc, fhs,\
           fk, fks, g1, g2, p2i, p2m, p2r, rk, s, tm, t1, t2, xx, yy,\
           elm, xd, yd, alas, as;
    int i, iflag, inu, k, kflag, kk, koded, j, ic, inub;
    double complex cy[2];

    int kmax =30;
    double r1 = 2.;
    double pi = 3.14159265358979324;
    double rthpi = 1.25331413731550025;
    double spi = 1.90985931710274403;
    double hpi = 1.57079632679489662;
    double fpi = 1.89769999331517738;
    double tth = 2. / 3.;
    double cc[8] = {
        5.77215664901532861e-01, -4.20026350340952355e-02,
       -4.21977345555443367e-02,  7.21894324666309954e-03,
       -2.15241674114950973e-04, -2.01348547807882387e-05,
        1.13302723198169588e-06,  6.11609510448141582e-09
    };
    xx = creal(z);
    yy = cimag(z);
    caz = cabs(z);
    cscl = 1. / tol;
    crsc = tol;
    double complex css[3] = {cscl, 1., crsc};
    double complex csr[3] = {crsc, 1., cscl};
    double bry[3] = {1e3*d1mach[0]/tol, tol/(1e3*d1mach[0]), d1mach[1]};
    int nz = 0;
    iflag = 0;
    koded = kode;
    rz = 2. / z;
    inu = (int)(fnu + 0.5);
    dnu = fnu - inu;
    if (fabs(dnu) != 0.5) {
        dnu2 = 0.0;
        if (fabs(dnu) > tol) { dnu2 = dnu * dnu; }
        if (caz <= r1) {
            //
            //    SERIES FOR ABS(Z) <= R1
            //
            fc = 1.;
            smu = clog(rz);
            fmu = smu * dnu;
            csh = csinh(fmu);
            cch = ccosh(fmu);
            if (dnu != 0.0) {
                fc = dnu * pi;
                fc *= 1. / sin(fc);
                smu = csh / dnu;
            }
            a2 = 1. + dnu;
            //
            // GAM(1-Z)*GAM(1+Z)=PI*Z/SIN(PI*Z), T1=1/GAM(1-DNU), T2=1/GAM(1+DNU)
            //
            t2 = exp(-gamln(a2));
            t1 = 1. / (t2*fc);
            if (fabs(dnu) <= 0.1) {
                //
                // SERIES FOR F0 TO RESOLVE INDETERMINACY FOR SMALL ABS(DNU)
                //
                ak = 1.;
                s = cc[0];
                for (int k = 2; k < 9; k++)
                {
                    ak *= dnu2;
                    tm = cc[k-1] * ak;
                    s += tm;
                    if (fabs(tm) < tol) { break; }
                }
                g1 = -s;
            } else {
                g1 = (t1-t2) / (dnu+dnu);
            }
            g2 = 0.5 * (t1+t2);
            f = fc*(g1*cch + smu*g2);
            pt = cexp(fmu);
            p = (0.5 / t2) * pt;
            q = (0.5 / t1) / pt;
            s1 = f;
            s2 = p;
            ak = 1.0;
            a1 = 1.0;
            ck = 1.0;
            bk = 1.0 - dnu2;
            if ((inu <= 0) && (n <= 1)) {
                //
                // GENERATE K(FNU,Z), 0.0D0  <=  FNU  <  0.5D0 AND N=1
                //
                if (caz >= tol) {
                    cz = z * z * 0.25;
                    t1 = 0.25 * caz * caz;
L30:
                    f = (f*ak + p + q) / bk;
                    p = p / (ak-dnu);
                    q = q / (ak+dnu);
                    rk = 1.0 / ak;
                    ck *= cz * rk;
                    s1 += ck * f;
                    a1 *= t1 * rk;
                    bk += ak + ak + 1.0;
                    ak += 1.0;
                    if (a1 > tol) { goto L30; }
                }
                y[0] = s1;
                if (koded == 1) { return nz; }
                y[0] = s1 * cexp(z);
                return nz;
            }
            //
            // GENERATE K(DNU,Z) AND K(DNU+1,Z) FOR FORWARD RECURRENCE
            //
            if (caz >= tol) {
                cz = z * z * 0.25;
                t1 = 0.25 * caz * caz;
L40:
                f = (f*ak + p + q) / bk;
                p *= 1.0 / (ak - dnu);
                q *= 1.0 / (ak + dnu);
                rk = 1. / ak;
                ck *= cz * rk;
                s1 += ck * f;
                s2 += ck * (p - f*ak);
                a1 *= t1 * rk;
                bk += ak + ak + 1.0;
                ak += 1.0;
                if (a1 > tol) { goto L40; }
            }
            kflag = 2;
            bk = creal(smu);
            a1 = fnu + 1.;
            ak = a1 * fabs(bk);
            if (ak > alim) { kflag = 3; }
            p2 = s2 * css[kflag-1];
            s2 = p2 * rz;
            s1 *= css[kflag-1];
            if (koded != 1) {
                f = cexp(z);
                s1 *= f;
                s2 *= f;
            }
            goto L100;
        }
    }
    //
    // IFLAG=0 MEANS NO UNDERFLOW OCCURRED
    // IFLAG=1 MEANS AN UNDERFLOW OCCURRED- COMPUTATION PROCEEDS WITH
    // KODED=2 AND A TEST FOR ON SCALE VALUES IS MADE DURING FORWARD
    // RECURSION
    //
    coef = rthpi / csqrt(z);
    kflag = 2;
    if (koded != 2) {
        if (xx > alim) { goto L200; }
        a1 = exp(-xx)*creal(css[kflag-1]);
        pt = a1*CMPLX(cos(yy), -sin(yy));
        coef *= pt;
    }

L50:
    if (fabs(dnu) == 0.5) {
        s1 = coef;
        s2 = coef;
        goto L100;
    }
//
//    MILLER ALGORITHM FOR ABS(Z) > R1
//
    ak = fabs(cos(pi*dnu));
    if (ak == 0.) {
        s1 = coef;
        s2 = coef;
        goto L100;
    }
    fhs = fabs(0.25 - dnu2);
    if (fhs == 0.) {
        s1 = coef;
        s2 = coef;
        goto L100;
    }
//
// COMPUTE R2=F(E). IF ABS(Z) >= R2, USE FORWARD RECURRENCE TO
// DETERMINE THE BACKWARD INDEX K. R2=F(E) IS A STRAIGHT LINE ON
// 12 <= E <= 60. E IS COMPUTED FROM 2**(-E)=B**(1-DIGITS(0.0_dp))=
// TOL WHERE B IS THE BASE OF THE ARITHMETIC.
//
    t1 = (i1mach[13] - 1)*d1mach[4]*(log(10)/log(2));
    t1 = fmin(fmax(t1, 12.0), 60.0);
    t2 = tth * t1 - 6.0;
    if (xx == 0.) {
        t1 = hpi;
    } else {
        t1 = fabs(atan(yy/xx));
    }
    if (t2 <= caz) {
        //
        // FORWARD RECURRENCE LOOP WHEN ABS(Z) >= R2
        //
        etest = ak / (pi*caz*tol);
        fk = 1.0;
        if (etest < 1.0) { goto L80; } 
        fks = 2.0;
        rk = caz + caz + 2.0;
        a1 = 0.0;
        a2 = 1.0;
        for (int i = 1; i < (kmax+1); i++)
        {
            ak = fhs / fks;
            bk = rk / (fk + 1.0);
            tm = a2;
            a2 = bk * a2 - ak * a1;
            a1 = tm;
            rk += 2.;
            fks += fk + fk + 2.0;
            fhs += fk + fk;
            fk += 1.0;
            tm = fabs(a2)*fk;
            if (etest < tm) {
                /* goto 160 */
                break;
            }
            if (i == kmax) {
                /* Didn't break so goes to 310 */
                return -2;
            }
        }

        /* 160 */
        fk += spi * t1 * sqrt(t2/caz);
        fhs = fabs(0.25 - dnu2);
    } else {
        //
        // COMPUTE BACKWARD INDEX K FOR ABS(Z) < R2
        //
        a2 = sqrt(caz);
        ak *= fpi / (tol*sqrt(a2));
        aa = 3.0 * t1 / (1.0 + caz);
        bb = 14.7 * t1 / (28.0 + caz);
        ak = (log(ak) + caz*cos(aa)/(1.0  + 0.008*caz)) / cos(bb);
        fk = 0.12125 * ak * ak / caz + 1.5;
    }
L80:
    //
    // BACKWARD RECURRENCE LOOP FOR MILLER ALGORITHM
    //
    k = (int)fk;
    fk = (double)k;
    fks = fk * fk;
    p1 = 0.0;
    p2 = tol;
    cs = p2;
    for (i=1; i < (k+1); i++)
    {
        a1 = fks - fk;
        a2 = (fks+fk) / (a1+fhs);
        rk = 2.0 / (fk + 1.);
        t1 = (fk + xx) * rk;
        t2 = yy * rk;
        pt = p2;
        p2 = (p2 * CMPLX(t1, t2) - p1) * a2;
        p1 = pt;
        cs += p2;
        fks = a1 - fk + 1.0;
        fk -= 1.0;
    }

    //
    // COMPUTE (P2/CS)=(P2/ABS(CS))*(CONJG(CS)/ABS(CS)) FOR BETTER SCALING
    //
    tm = cabs(cs);
    pt = 1.0 / tm;
    s1 = pt * p2;
    cs = conj(cs) * pt;
    s1 *= coef * cs;
    if ((inu <= 0) && (n <= 1)) {
        zd = z;
        if (iflag == 1) { goto L190; }
        goto L130;
    }
    //
    // COMPUTE P1/P2=(P1/ABS(P2)*CONJG(P2)/ABS(P2) FOR SCALING
    //
    tm = cabs(p2);
    pt = 1.0 / tm;
    p1 = pt * p1;
    p2 = conj(p2) * pt;
    pt = p1 * p2;
    s2 = s1 * (1. + (dnu+0.5 - pt)/z);
    //
    // FORWARD RECURSION ON THE THREE TERM RECURSION RELATION WITH
    // SCALING NEAR EXPONENT EXTREMES ON KFLAG=1 OR KFLAG=3
    //
L100:
    ck = (dnu + 1.)*rz;
    if (n == 1) { inu -= 1; }
    if (inu <= 0) {
        if (n <= 1) { s1 = s2; }
        zd = z;
        if (iflag == 1) { goto L190; }
        goto L130;
    }
    inub = 1;
    if (iflag == 1) { goto L160; }
L110:
    p1 = csr[kflag-1];
    ascle = bry[kflag-1];
    for (int i = inub; i < inu+1; i++)
    {
        st = s2;
        s2 = ck*s2 + s1;
        s1 = st;
        ck += rz;
        if (kflag < 3) {
            p2 = s2*p1;
            p2m = fmax(fabs(creal(p2)), fabs(cimag(p2)));
            if (p2m > ascle) {
                kflag += 1;
                ascle = bry[kflag-1];
                s1 *= p1;
                s2 = p2;
                s1 *= css[kflag-1];
                s2 *= css[kflag-1];
                p1 = csr[kflag-1];
            }
        }
    }
    if (n == 1) { s1 = s2; }
    
L130:
    y[0] = s1 * csr[kflag-1];
    if (n == 1) { return nz; }
    y[1] = s2 * csr[kflag-1];
    if (n == 2) { return nz; }
    kk = 2;
L140:
    kk += 1;
    if (kk > n) { return nz; }
    p1 = csr[kflag-1];
    ascle = bry[kflag-1];
    for (int i = kk; i < (n+1); i++)
    {
        p2 = s2;
        s2 = ck*s2 + s1;
        s1 = p2;
        ck += rz;
        p2 = s2*p1;
        y[i-1] = p2;
        if (kflag < 3) {
            p2m = fmax(fabs(creal(p2)), fabs(cimag(p2)));
            if (p2m > ascle) {
                kflag += 1;
                ascle = bry[kflag-1];
                s1 *= p1;
                s2 = p2;
                s1 *= css[kflag-1];
                s2 *= css[kflag-1];
                p1 = csr[kflag-1];
            }
        }
    }
    return nz;
//
// IFLAG=1 CASES, FORWARD RECURRENCE ON SCALED VALUES ON UNDERFLOW
//
L160:
    elm = exp(-elim);
    ascle = bry[0];
    zd = z;
    xd = xx;
    yd = yy;
    ic = -1;
    j = 2;
    for (int i = 1; i < (inu+1); i++)
    {
        st = s2;
        s2 = ck*s2 + s1;
        s1 = st;
        ck += rz;
        as = cabs(s2);
        alas = log(as);
        p2r = alas - xd;
        if (p2r >= -elim) {
            p2 = -zd + clog(s2);
            p2r = creal(p2);
            p2i = cimag(p2);
            p2m = exp(p2r) / tol;
            p1 = p2m * CMPLX(cos(p2i), sin(p2i));
            if (!(uchk(p1, ascle, tol))) {
                j = 3 - j;
                cy[j-1] = p1;
                if (ic == i-1) { goto L180; }
                ic = i;
                continue;
            }
        }
        if (alas >= 0.5 * elim) {
            xd -= elim;
            s1 *= elm;
            s2 *= elm;
            zd = CMPLX(xd, yd);
        }
    }
    if (n == 1) { s1 = s2; }
    goto L190;
L180:
    kflag = 1;
    inub = i + 1;
    s2 = cy[j-1];
    j = 3 - j;
    s1 = cy[j-1];
    if (inub <= inu) { goto L110; }
    if (n == 1) { s1 = s2; }
    goto L130;
L190:
    y[0] = s1;
    if (n != 1) { y[1] = s2; }
    ascle = bry[0];
    nz = kscl(zd, fnu, n, &y[0], rz, &ascle, tol, elim);
    inu = n - nz;
    if (inu < 0) { return nz; }
    kk = nz + 1;
    s1 = y[kk-1];
    y[kk-1] = s1 * csr[0];
    if (inu == 1) { return nz; }
    kk = nz + 2;
    s2 = y[kk-1];
    y[kk-1] = s2 * csr[0];
    if (inu == 2) { return nz; }
    t2 = fnu + (kk-1);
    ck = t2 * rz;
    kflag = 1;
    goto L140;
L200:
    koded = 2;
    iflag = 1;
    kflag = 2;
    goto L50;
}


double gamln(double z) {
    int i1m, mz;
    double fln, fz, rln, s, tlg, trm, tst, t1, wdtol, zdmy, zinc, zm, zmin, zp, zsq;
    const double con = 1.83787706640934548;
    int nz = 0;
    if (z > 0.0) {
        if (z <= 101.) {
            nz = (int)z;
            fz = z - nz;
            if (fz <= 0.0) {
                if (nz <= 100) {
                    return dgamln_gln[nz-1];
                }
            }
        }
        wdtol = fmax(d1mach[3], 1e-18);
        i1m = i1mach[13];
        rln = d1mach[4]*i1m;
        fln = fmax(fmin(rln, 20.), 3.) - 3.;
        zm = 1.8 + 0.3875*fln;
        mz = zm + 1;
        zmin = mz;
        zdmy = z;
        zinc = 0.;
        if (z < zmin){
            zinc = zmin - nz;
            zdmy = z + zinc;
        }
        zp = 1. / zdmy;
        t1 = dgamln_cf[0]*zp;
        s = t1;
        if (zp >= wdtol) {
            zsq = zp*zp;
            tst = t1*wdtol;
            for (int i = 1; i < 22; i++)
            {
                zp *= zsq;
                trm = dgamln_cf[i]*zp;
                if (fabs(trm) < tst) {
                    break;
                }
                s += trm;
            }
            
        }

        if (zinc == 0.) {
            tlg = log(z);
            return z*(tlg-1.) + 0.5*(con-tlg) + s;
        }
        zp = 1.;
        nz = zinc;
        for (int i = 0; i < nz; i++)
        {
            zp *= (z + i);
        }
        tlg = log(zdmy);
        return zdmy*(tlg-1.) - log(zp) + 0.5*(con-tlg) + s;
    }
    // Zero or negative argument
    return NAN;
}


int mlri(
    double complex z,
    double fnu,
    int kode,
    int n,
    double complex *y,
    double tol
) {
    double complex ck, cnorm, pt, p1, p2, rz, sum;
    double ack, ak, ap, at, az, bk, fkap, fkk, flam, fnf, rho,\
           rho2, scle, tfnf, tst, x;
    int i, iaz, ifnu, inu, itime, k, kk, km, m, nz;
    scle = d1mach[0] / tol;
    nz = 0;
    az = cabs(z);
    x = creal(z);
    iaz = (int)az;
    ifnu = (int)fnu;
    inu = ifnu + n - 1;
    at = iaz + 1;
    ck = at / z;
    rz = 2. / z;
    p1 = 0.;
    p2 = 1.;
    ack = (at + 1.0) / az;
    rho = ack + sqrt(ack*ack - 1.);
    rho2 = rho * rho;
    tst = (rho2 + rho2) / ((rho2 - 1.0)*(rho - 1.0));
    tst /= tol;
    //
    // COMPUTE RELATIVE TRUNCATION ERROR INDEX FOR SERIES
    //
    ak = at;
    i = 1;
    for (i = 1; i < 81; i++ )
    {
        pt = p2;
        p2 = p1 - ck * p2;
        p1 = pt;
        ck += rz;
        ap = cabs(p2);
        if (ap > tst*ak*ak) { break; }
        ak += 1.0;
        if (i == 80) {
            /* Exhausted loop without break */
            return -2;
        }
    }
    i += 1;
    k = 0;
    if (inu >= iaz) {
    //
    // COMPUTE RELATIVE TRUNCATION ERROR FOR RATIOS
    //
        p1 = 0.0;
        p2 = 1.0;
        at = inu + 1;
        ck = at / z;
        ack = at / az;
        tst = sqrt(ack / tol);
        itime = 1;
        k = 1;
        for (k = 1; k < 81; k++ )
        {
            pt = p2;
            p2 = p1 - ck * p2;
            p1 = pt;
            ck += rz;
            ap = cabs(p2);
            if (ap >= tst) {
                if (itime == 2) { break; }
                ack = cabs(ck);
                flam = ack + sqrt(ack*ack - 1.0);
                fkap = ap / cabs(p1);
                rho = fmin(flam, fkap);
                tst *= sqrt(rho / (rho*rho - 1.0));
                itime = 2;
            }
            if (i == 80) {
                /* Exhausted loop without break */
                return -2;
            }
        }
    }
    //
    // BACKWARD RECURRENCE AND SUM NORMALIZING RELATION
    //
    k += 1;
    kk = fmax(i+iaz, k+inu);
    fkk = kk;
    p1 = 0.0;
    //
    // SCALE P2 AND SUM BY SCLE
    //
    p2 = scle;
    fnf = fnu - ifnu;
    tfnf = fnf + fnf;
    bk = gamln(fkk + tfnf + 1.0) - gamln(fkk + 1.0) - gamln(tfnf + 1.0);
    bk = exp(bk);
    sum = 0.;
    km = kk - inu;
    for (i = 1; i < (km+1); i++)
    {
        pt = p2;
        p2 = p1 + (fkk + fnf)*rz*p2;
        p1 = pt;
        ak = 1. - tfnf / (fkk+tfnf);
        ack = bk*ak;
        sum += (ack + bk)*p1;
        bk = ack;
        fkk -= 1.;
    }
    y[n-1] = p2;
    if (n != 1) {
        for (i = 2; i < (n+1); i++)
        {
            pt = p2;
            p2 = p1 + (fkk + fnf)*rz*p2;
            p1 = pt;
            ak = 1. - tfnf / (fkk+tfnf);
            ack = bk*ak;
            sum += (ack + bk)*p1;
            bk = ack;
            fkk -= 1.;
            m = n - i + 1;
            y[m-1] = p2;
        }
    }
    if (ifnu > 0) {
        for (i = 1; i < (ifnu+1); i++)
        {
            pt = p2;
            p2 = p1 + (fkk + fnf)*rz*p2;
            p1 = pt;
            ak = 1. - tfnf / (fkk+tfnf);
            ack = bk*ak;
            sum += (ack + bk)*p1;
            bk = ack;
            fkk -= 1.;
        }
    }
    pt = z;
    if (kode == 2) { pt -= x; }
    p1 = -fnf * clog(rz) + pt;
    ap = gamln(1. + fnf);
    pt = p1 - ap;
    //
    // THE DIVISION EXP(PT)/(SUM+P2) IS ALTERED TO AVOID OVERFLOW
    // IN THE DENOMINATOR BY SQUARING LARGE QUANTITIES
    //
    p2 += sum;
    ap = cabs(p2);
    p1 = 1. / ap;
    ck = cexp(pt) * p1;
    pt = conj(p2)*p1;
    cnorm = ck * pt;
    for (int i = 0; i < n; i++) { y[i] *= cnorm; }
    return nz;
}


int kscl(
    double complex zr,
    double fnu,
    int n,
    double complex *y,
    double complex rz,
    double *ascle,
    double tol,
    double elim
) {
    double complex cy[2] = { 0. };
    double as, acs, alas, fn, zri, xx;
    double complex s1, s2, cs, ck, zd;
    int nz = 0;
    int ic = 0;
    int nn = (3 <= n+1? 3 : n + 1);
    int kk = 0;
    double elm = exp(-elim);

    for (int i = 0; i < nn; i++)
    {
        s1 = y[i];
        cy[i] = s1;
        as = cabs(s1);
        acs = -creal(zr) + log(as);
        nz += 1;
        y[i] = 0.;
        if (acs < -elim) {
            continue;
        }
        cs = -zr + clog(s1);
        cs = (exp(creal(cs))/tol)*(cos(cimag(cs)) + sin(cimag(cs)*I));
        if (!uchk(cs, *ascle, tol)) {
            y[i] = cs;
            nz -= 1;
            ic = i;
        }
    }
    if (n == 1) {
        return nz;
    }
    if (ic <= 1) {
        y[0] = 0.;
        nz = 2;
    }
    if (n == 2) {
        return nz;
    }
    fn = fnu + 1.;
    ck = fn*rz;
    s1 = cy[0];
    s2 = cy[1];
    zri = cimag(zr);
    zd = zr;
    for (int i = 3; i < (n+1); i++)
    {
        kk = i;
        cs = s2;
        s2 *= ck;
        s2 += s1;
        s1 = cs;
        ck += rz;
        as = cabs(s2);
        alas = log(as);
        acs = alas - xx;
        nz += 1;
        y[i-1] = 0.;
        if (acs >= -elim) {
            cs = clog(s2);
            cs -= zd;
            cs = (exp(creal(cs))/tol)*(cos(cimag(cs)) + sin(cimag(cs)*I));
            if (!uchk(cs, *ascle, tol)) {
                y[i-1] = cs;
                nz -= 1;
                if (ic == kk-1) {
                    nz = kk - 2;
                    for (int i = 0; i < nz; i++)
                    {
                        y[i] = 0.;
                    }
                    return nz;
                }
                ic = kk;
                continue;
            }
            if (alas >= 0.5*elim){
                xx -= elim;
                s1 *= elm;
                s2 *= elm;
                zd = xx + zri*I;
            }
        }
    }
    nz = n;
    if (ic == n) {
        nz = n-1;
    } else {
        nz = kk - 2;
    }
    for (int i = 0; i < nz; i++)
    {
        y[i] = 0.;
    }
    return nz;
}


int seri(
    double complex z,
    double fnu,
    int kode,
    int n,
    double complex *y,
    double tol,
    double elim,
    double alim
) {
    double complex ak1, ck, coef, crsc, cz, hz, rz, s1, s2, w[2];
    double aa, acz, ak, arm, ascle, atol, az, dfnu, fnup, rak1,\
           rs, rtr1, s, ss, x;
    int ib, iflag, il, k, l, m, nn;

    int nz = 0;
    az = cabs(z);
    if (az == 0.0) {
        y[0] = 0.0;
        if (fnu == 0.) { y[0] = 1.0; }
        if (n == 1) { return nz; }
        for (int i = 1; i < n; i++) { y[i] = 0.0; }
        return nz;
    }
    x = creal(z);
    arm = 1e3*d1mach[0];
    rtr1 = sqrt(arm);
    crsc = 1.0;
    iflag = 0;
    if (az >= arm) {
        hz = z*0.5;
        cz = 0.;
        if (az > rtr1) { cz = hz*hz; }
        acz = cabs(cz);
        nn = n;
        ck = clog(hz);
L10:
        dfnu = fnu + (nn-1);
        fnup = dfnu + 1.0;
        //
        // UNDERFLOW TEST
        //
        ak1 = ck * dfnu;
        ak = gamln(fnup);
        ak1 -= ak;
        if (kode == 2) { ak1 -= x; }
        rak1 = creal(ak1);
        if (rak1 > -elim) { goto L30; }
L20:
        nz += 1;
        y[nn - 1] = 0.0;
        //
        // RETURN WITH NZ < 0 IF ABS(Z*Z/4) > FNU+N-NZ-1 COMPLETE
        // THE CALCULATION IN CBINU WITH N=N-ABS(NZ)
        //
        if (acz > dfnu) { return -nz; }
        nn -= 1;
        if (nn == 0) { return nz; }
        goto L10;
L30:
        if (rak1 <= -alim) {
            iflag = 1;
            ss = 1.0 / tol;
            crsc = tol;
            ascle = arm * ss;
        }
        ak = cimag(ak1);
        aa = exp(rak1);
        if (iflag == 1) { aa *= ss; }
        coef = aa * (cos(ak) + sin(ak)*I);
        atol = tol * acz / fnup;
        il = (nn > 2 ? 2 : nn);
        for (int i = 1; i < (il +1); i++)
        {
            dfnu = fnu + (nn-i);
            fnup = dfnu + 1.0;
            s1 = 1.0;
            if (acz >= tol*fnup) {
                ak1 = 1.0;
                ak = fnup + 2.0;
                s = fnup;
                aa = 2.0;
L40:
                rs = 1.0 / s;
                ak1 *= cz * rs;
                s1 += ak1;
                s += ak;
                ak += 2.0;
                aa *= acz * rs;
                if (aa > atol) { goto L40; }
            }
            m = nn - i + 1;
            s2 = s1 * coef;
            w[i-1] = s2;
            if (iflag != 0) {
                if (uchk(s2, ascle, tol)) { goto L20; }
            }
            y[m-1] = s2 * crsc;
            if (i != il) { coef *= dfnu / hz; }
        }
        if (nn <= 2) { return nz; }
        k = nn - 2;
        ak = k;
        rz = 2.0 / z;
        if (iflag == 1) { goto L80; }
        ib = 3;
L60:
        for (int i = ib; i < (nn+1); i++)
        {
            y[k-1] = (ak+fnu)*rz*y[k] + y[k+1];
            ak -= 1.0;
            k -= 1;
        }
        return nz;
L80:
        s1 = w[0];
        s2 = w[1];
        l = 3;
        for (int l = 3; l < (nn+1); l++)
        {
            ck = s2;
            s2 = s1 + (ak+fnu)*rz*s2;
            s1= ck;
            ck = s2*crsc;
            y[k-1] = ck;
            ak -= 1.0;
            k -= 1;
            if (cabs(ck) > ascle) { goto L100; }
        }
        return nz;
L100:
        ib = l+1;
        if (ib > nn) { return nz; }
        goto L60;
    }
    nz = n;
    if (fnu == 0.0) { nz -= 1; }
    y[0] = 0.0;
    if (fnu == 0.) { y[0] = 1.0; }
    if (n == 1) { return nz; }
    for (int i = 1; i < n; i++) { y[i] = 0.0; }
    return nz;
}


int s1s2(
    double complex zr,
    double complex *s1,
    double complex *s2,
    double ascle,
    double alim,
    int *iuf
) {
    double complex c1, s1d;
    double aa, aln, as1, as2, xx;
    int nz = 0;
    as1 = cabs(*s1);
    as2 = cabs(*s2);
    aa = creal(*s1);
    aln = cimag(*s1);

    if ((aa != 0.) || (aln != 0.)) {
        if (as1 != 0.){
            xx = creal(zr);
            aln = -xx - xx + log(as1);
            s1d = *s1;
            *s1 = 0.;
            as1 = 0.;
            if (aln >= -alim) {
                c1 = clog(s1d) - zr - zr;
                *s1 = cexp(c1);
                as1 = cabs(*s1);
                *iuf += 1;
            }
        }
    }
    aa = fmax(as1, as2);
    if (aa > ascle) {
        return nz;
    }
    *s1 = 0.;
    *s2 = 0.;
    *iuf = 0;
    return 1;
}


int uchk(
    double complex y,
    double ascle,
    double tol
) {
    double yr = fabs(creal(y));
    double yi = fabs(cimag(y));
    double ss = fmax(yr, yi);
    double st = fmin(yr, yi);
    if (st > ascle) {
        return 0;
    } else {
        st /= tol;
        if (ss < st) {
            return 1;
        } else {
            return 0;
        }
    }
}


void unhj(
    double complex z,
    double fnu,
    int ipmtr,
    double tol,
    double complex *phi,
    double complex *arg,
    double complex *zeta1,
    double complex *zeta2,
    double complex *asum,
    double complex *bsum
) {
    double complex cfnu, przth, ptfn, rtzta, rzth, suma, sumb;
    double complex tfn, t2, w, w2, za, zb, zc, zeta, zth;
    double ang, atol, aw2, azth, btol, fn13, fn23, pp, rfn13;
    double rfnu, rfnu2, wi, wr, zci, zcr, zetai, zetar, zthi;
    double zthr, asumr, asumi, bsumr, bsumi, test, tstr, tsti, ac;
    double ex1 = 1./3.;
    double ex2 = 2./3.;
    double hpi = 1.57079632679489662;
    double pi = 3.14159265358979324;
    double thpi = 4.71238898038468986;
    int ias, ibs, j, ju, k, kmax, kp1, ks, l, lrp1, l1, l2, m;
    /* array vars */
    double complex cr[14] = { 0. };
    double complex dr[14] = { 0. };
    double complex up[14] = { 0. };
    double complex p[30] = { 0. };
    double ap[30] = { 0. };

    rfnu = 1. / fnu;
    tstr = creal(z);
    tsti = cimag(z);
    test = d1mach[0] * 1e3;
    ac = fnu*test;
    if ((fabs(tstr) <= ac) && (fabs(tsti) <= ac)) {
        ac = 2.*fabs(log(test)) + fnu;
        *zeta1 = ac;
        *zeta2 = fnu;
        *phi = 1.;
        *arg = 1.;
        return;
    }
    zb = z*rfnu;
    rfnu2 = rfnu*rfnu;

    fn13 = pow(fnu, ex1);
    fn23 = fn13 * fn13;
    rfn13 = 1./fn13;
    w2 = 1. - zb*zb;
    aw2 = cabs(w2);
    if (aw2 <= 0.25) {
        k = 1;
        p[0] = 1.;
        suma = zunhj_gama[0];
        ap[0] = 1.;
        if (aw2 >= tol) {
            for (int k = 2; k < 31; k++)
            {
                p[k-1] = p[k-2]*w2;
                suma += p[k-1]*zunhj_gama[k-1];
                ap[k-1] = ap[k-2]*aw2;
                if (ap[k-1] < tol) { break; }
            }
        }

        kmax = k;
        zeta = w2*suma;
        *arg = zeta*fn23;
        za = sqrt(suma);
        *zeta2 = sqrt(w2)*fnu;
        *zeta1 = *zeta2 * (1. + zeta*za*ex2);
        za = za + za;
        *phi = sqrt(za)*rfn13;
        if (ipmtr == 1) { return; }

        sumb = 0.;
        for (k = 1; k < kmax+1; k++) {
            sumb += p[k-1]*zunhj_beta[k-1];
        }
        *asum = 0.;
        *bsum = sumb;
        l1 = 0;
        l2 = 30;
        btol = tol * (fabs(creal(*bsum)) + fabs(cimag(*bsum)));
        atol = tol;
        pp = 1.;
        ias = 0;
        ibs = 0;
        if (rfnu2 < tol) {
            *asum += 1.;
            *bsum *= rfnu*rfn13;
            return;
        }
        for (int is = 2; is < 8; is++)
        {
            atol /= rfnu2;
            pp *= rfnu2;
            if (ias != 1) {
                suma = 0.;
                for (int k = 1; k < (kmax+1); k++)
                {
                    m = l1 + k;
                    suma += p[k-1]*zunhj_alfa[m-1];
                    if (ap[k-1] < atol) { return; }
                }
                *asum += suma*pp;
                if (pp < tol) { ias = 1; }
            }
            if (ibs != 1) {
                sumb = 0.;
                for (int k = 1; k < (kmax+1); k++)
                {
                    m = l2 + k;
                    sumb += p[k-1]*zunhj_beta[m-1];
                    if (ap[k-1] < atol) { return; }
                }
                *bsum += sumb*pp;
                if (pp < btol) { ibs = 1; }
            }
            if ((ias == 1) && (ibs == 1)) { return; }
            l1 += 30;
            l2 += 30;
        }
        *asum += 1.;
        *bsum *= rfnu*rfn13;
        return;
    } else {
        w = csqrt(w2);
        wr = creal(w);
        wi = cimag(w);
        if (wr < 0) { wr = 0.;}
        if (wi < 0) { wi = 0.;}
        w = wr + wi*I;
        za = (1. + w) / zb;
        zc = clog(za);
        zcr = creal(zc);
        zci = cimag(zc);
        if (zci < 0) { zci = 0.;}
        if (zci > hpi) { zci = hpi;}
        if (zcr < 0) { zcr = 0.;}
        zc = zcr + zci*I;
        zth = (zc-w)*1.5;
        cfnu = fnu;
        *zeta1 = zc*cfnu;
        *zeta2 = w*cfnu;
        azth = cabs(zth);
        zthr = creal(zth);
        zthi = cimag(zth);
        ang = thpi;
        if ((zthr < 0.) || (zthi >= 0.)) {
            ang = hpi;
            if (zthr != 0.) {
                ang = atan(zthi/zthr);
                if (zthr < 0.) { ang += pi; }
            }
        }
        pp = pow(azth, ex2);
        ang *= ex2;
        zetar = pp * cos(ang);
        zetai = pp * sin(ang);
        if (zetai < 0.) { zetai = 0.; }
        zeta = zetar + zetai*I;
        *arg = zeta*fn23;
        rtzta = zth / zeta;
        za = rtzta / w;
        *phi = csqrt(za + za) * rfn13;
        if (ipmtr == 1) { return; }
        tfn = rfnu / w;
        rzth = rfnu / zth;
        zc = rzth * zunhj_ar[1];
        t2 = 1. / w2;
        up[1] = (t2*zunhj_c[1] + zunhj_c[2])*tfn;
        *bsum = up[1] + zc;
        *asum = 0.;

        if (rfnu < tol) {
            *asum += 1.;
            *bsum *= -rfn13 / rtzta;
            return;
        }

        przth = rzth;
        ptfn = tfn;
        up[0] = 1.;
        pp = 1.;
        bsumr = creal(*bsum);
        bsumi = cimag(*bsum);
        btol = tol * (fabs(bsumr) + fabs(bsumi));
        ks = 0;
        kp1 = 2;
        l = 3;
        ias = 0;
        ibs = 0;

        for (int lr = 2; lr < 13; lr += 2)
        {
            lrp1 = lr + 1;
            for (int k = lr; k < (lrp1+1); k++)
            {
                ks += 1;
                kp1 += 1;
                l += 1;
                za = zunhj_c[l-1];
                for (int j = 2; j < (kp1+1); j++)
                {
                    l += 1;
                    za = za*t2 + zunhj_c[l-1];
                }
                ptfn *= tfn;
                up[kp1-1] = ptfn*za;
                cr[ks-1] = przth*zunhj_br[ks];
                przth *= rzth;
                dr[ks-1] = przth*zunhj_ar[ks+1];
            }
            pp *= rfnu2;
            if (ias != 1) {
                suma = up[lr];
                ju = lrp1;
                for (int jr = 1; j < lrp1; j++)
                {
                    ju -= 1;
                    suma += cr[jr-1] * up[ju-1];
                }
                *asum += suma;
                asumr = creal(*asum);
                asumi = cimag(*asum);
                test = fabs(asumr) + fabs(asumi);
                if ((pp < tol) && (test < tol)) { ias = 1; }
            }
            if (ibs != 1) {
                sumb = up[lr+1] + up[lr]*zc;
                ju = lrp1;
                for (int jr = 1; j < lrp1; j++)
                {
                    ju -= 1;
                    sumb += dr[jr-1] * up[ju-1];
                }
                *bsum += sumb;
                bsumr = creal(*bsum);
                bsumi = cimag(*bsum);
                test = fabs(bsumr) + fabs(bsumi);
                if ((pp < tol) && (test < tol)) { ibs = 1; }
            }
            if ((ias == 1) && (ibs == 1)) { break; }
        }
        *asum += 1.;
        *bsum *= -rfn13 / rtzta;
        return;
    }
}


void uni1(
    double complex z,
    double fnu,
    int kode,
    int n,
    double complex *y,
    int *nz,
    int *nlast,
    double fnul,
    double tol,
    double elim,
    double alim
) {
    double complex cfn, crsc, cscl, c1, c2, phi, rz, sum, s1, s2, zeta1, zeta2;
    double aphi, ascle, c2i, c2m, c2r, fn, rs1, yy;
    int iflag, init, k, m, nd, nn, resetfor = 0;
    double complex cwrk[16] = { 0. };
    double complex cy[2] = { 0. };
    nz = 0;
    nd = n;
    nlast = 0;
    cscl = 1.;
    crsc = tol;
    double complex css[3] = {cscl, 1., crsc};
    double complex csr[3] = {crsc, 1., cscl};
    double bry[3] = {1e3*d1mach[0]/tol, 0., 0.};
    fn = fmax(fnu, 1.);
    init = 0;
    unik(z, fn, 1, 1, tol, &init, &phi, &zeta1, &zeta2, &sum, &cwrk[0]);
    if (kode != 1) {
        cfn = fn;
        s1 = -zeta1 + cfn * (cfn/(z+zeta2));
    } else {
        s1 = zeta2 - zeta1;
    }
    rs1 = creal(s1);
    if (fabs(rs1) > elim) {
        if (rs1 > 0) {
            *nz = -1;
            return;
        }
        *nz = n;
        for (int i = 0; i < n; i++) { y[i] = 0.; }
    }

    while (1) {
        if (resetfor == 1) { resetfor = 0; }
        nn = (nd > 2 ? 2 : nd);
        for (int i = 1; i < (nn+1); i++)
        {
            fn = fnu + (nd-i);
            init = 0;
            unik(z, fn, 1, 0, tol, &init, &phi, &zeta1, &zeta2, &sum, &cwrk[0]);
            if (kode != 1) {
                cfn = fn;
                yy = cimag(z);
                s1 = -zeta1 + cfn*(cfn/(z/zeta2)) + yy*I;
            } else {
                s1 = zeta2 - zeta1;
            }
            //
            // TEST FOR UNDERFLOW AND OVERFLOW
            //
            rs1 = creal(s1);
            if (fabs(rs1) > elim) {
                if (rs1 <= 0.) {
                    y[nd-1] = 0.;
                    nz += 1;
                    nd -= 1;
                    if (nd == 0) { return; }
                    int nuf = uoik(z, fnu, kode, 1, nd, &y[0], tol, elim, alim);
                    if (nuf >= 0) {
                        nd -= nuf;
                        nz += nuf;
                        if (nd == 0) { return; }
                        fn = fnu + (nd -1);
                        /* Resetting for loop (GOTO 30) */
                        if (fn >= fnul) {
                            resetfor = 1;
                            break;
                        }
                        *nlast = nd;
                        return;
                    }
                }
            }
            if (i == 1) { iflag = 2; }
            if (fabs(rs1) >= alim) {
                //
                // REFINE TEST AND SCALE
                //
                aphi = cabs(phi);
                rs1 += log(aphi);

                /* another go to 110 */
                if (fabs(rs1) > elim) {
                    if (rs1 <= 0.) {
                        y[nd-1] = 0.;
                        nz += 1;
                        nd -= 1;
                        if (nd == 0) { return; }
                        int nuf = uoik(z, fnu, kode, 1, nd, &y[0], tol, elim, alim);
                        if (nuf >= 0) {
                            nd -= nuf;
                            nz += nuf;
                            if (nd == 0) { return; }
                            fn = fnu + (nd -1);
                            /* Resetting for loop (GOTO 30) */
                            if (fn >= fnul) {
                                resetfor = 1;
                                break;
                            }
                            *nlast = nd;
                            return;
                        }
                    }
                }
                if (i == 1) { iflag = 1; }
                if ((rs1 >= 0.) && (i == 1)) {
                    iflag = 3;
                }
            }
            //
            // SCALE S1 IF ABS(S1) < ASCLE
            //
            s2 = phi * sum;
            c2r = creal(s1);
            c2i = cimag(s1);
            c2m = exp(c2r)*creal(css[iflag-1]);
            s1 = c2m * (cos(c2i) + sin(c2i)*I);
            s2 *= s1;
            if (iflag == 1) {
                if (!(uchk(s2, bry[0], tol))) {
                    /* another go to 110 */
                    if (rs1 <= 0.) {
                        y[nd-1] = 0.;
                        nz += 1;
                        nd -= 1;
                        if (nd == 0) { return; }
                        int nuf = uoik(z, fnu, kode, 1, nd, &y[0], tol, elim, alim);
                        if (nuf >= 0) {
                            nd -= nuf;
                            nz += nuf;
                            if (nd == 0) { return; }
                            fn = fnu + (nd -1);
                            /* Resetting for loop (GOTO 30) */
                            if (fn >= fnul) {
                                resetfor = 1;
                                break;
                            }
                            *nlast = nd;
                            return;
                        }
                    }
                }
            }
            m = nd - i + 1;
            cy[i-1] = s2;
            y[m-1] = s2*csr[iflag-1];
        }
        /* Get out of while loop */
        if (resetfor == 0) { break; }
    }    
    if (nd <= 2) { return; }

    rz = 2. / z;
    bry[1] = 1. / bry[0];
    bry[2] = d1mach[1];
    s1 = cy[0];
    s2 = cy[1];
    c1 = csr[iflag-1];
    ascle = bry[iflag-1];
    k = nd - 2;
    fn = k;
    for (int i = 3; i < nd+1; i++)
    {
        c2 = s2;
        s2 = s1 + (fnu+fn)*rz*s2;
        s1 = c2;
        c2 = s2*c1;
        y[k-1] = c2;
        k -= 1;
        fn -= 1.;
        if (iflag < 3) {
            c2r = fabs(creal(c2));
            c2i = fabs(cimag(c2));
            c2m = fmax(c2r, c2i);
            if (c2m > ascle) {
                iflag += 1;
                ascle = bry[iflag-1];
                s1 *= c1;
                s2 = c2;
                s1 *= css[iflag-1];
                s2 *= css[iflag-1];
                c1 = csr[iflag-1];
            }
        }
    }
    return;
}


void unik(
    double complex zr,
    double fnu,
    int ikflg,
    int ipmtr,
    double tol,
    int *init,
    double complex *phi,
    double complex *zeta1,
    double complex *zeta2,
    double complex *total,
    double complex *cwrk
) {
    double complex cfn, crfn, s, sr, t, t2, zn;
    double ac, rfn, test, tstr, tsti;
    int k, l;
    double con[2] = { 3.98942280401432678, 1.25331413731550025 };

    if (init == 0) {
        rfn = 1. / fnu;
        crfn = rfn;

        tstr = creal(zr);
        tsti = cimag(zr);
        test = d1mach[0] * 1e3;
        ac = fnu * test;
        if ((fabs(tstr) <= ac) && (fabs(tsti) <= ac)) {
            ac = 2.*fabs(log(test)) + fnu;
            *zeta1 = ac;
            *zeta2 = fnu;
            *phi = 1.;
        }
        t = zr * crfn;
        s = 1. + t*t;
        sr = sqrt(s);
        cfn = fnu;
        zn = (1. + sr) / t;
        *zeta1 = cfn * log(zn);
        *zeta2 = cfn * sr;
        t = 1. / sr;
        sr = t*crfn;
        cwrk[15] = sqrt(sr);
        *phi = sqrt(sr)*con[ikflg-1];
        if (ipmtr != 0) { return; }
        t2 = 1. / s;
        cwrk[0] = 1.;
        crfn = 1.;
        ac = 1.;
        l = 1;
        k = 2;
        for (int k = 2; k < 16; k++)
        {
            s = 0.;
            for (int j = 1; j < (k+1); j++)
            {
                l += 1;
                s = s*t2 + zunik_c[l-1];
            }
            crfn *= sr;
            cwrk[k-1] = crfn*s;
            ac *= rfn;
            tstr = creal(cwrk[k-1]);
            tsti = cimag(cwrk[k-1]);
            test = fabs(tstr) + fabs(tsti);
            if ((ac < tol) && (test < tol)) {
                break;
            }
        }
        *init = k;
    }
    
    if (ikflg != 2) {
        *total = 0.;
        for (int i = 0; i < (k+1); i++) { *total += cwrk[i]; }
        *phi = cwrk[15] * con[0];
        return;
    }

    s = 0.;
    t = 1.;
    for (int i = 1; i < (k+1); i++) {
        s += t*cwrk[i];
        t = -t;
    }
    *total = s;
    *phi = cwrk[15] * con[1];
    return;
}


int uoik(
    double complex z,
    double fnu,
    int kode,
    int ikflg,
    int n,
    double complex *y,
    double tol,
    double elim,
    double alim
) {
    double complex arg, asum, bsum, cz, phi, sum, zb, zeta1;
    double complex zeta2, zn, zr;
    double aarg, aphi, ascle, ax, ay, fnn, gnn, gnu, rcz, x, yy;
    int iform, init, nn;
    double aic = 1.265512123484645396;
    double complex cwrk[16] = { 0. };

    int nuf = 0;
    nn = n;
    x = creal(z);
    zr = z;
    if (x < 0.) { zr = -z; }
    zb = zr;
    yy = cimag(zr);
    ax = fabs(x) * sqrt(3.);
    ay = fabs(yy);
    iform = 1;
    if (ay > ax) { iform = 2; }
    gnu = fmax(fnu, 1.);
    if (ikflg != 1) {
        fnn = nn;
        gnn = fnu + fnn -1;
        gnu = fmax(gnn, fnn);
    }

    if (iform != 2) {
        init = 0;
        unik(zr, gnu, ikflg, 1, tol, &init, &phi, &zeta1, &zeta2, &sum, &cwrk[0]);
        cz = -zeta1 + zeta2;
    } else {
        zn = -zr * I;
        if (yy <= 0.) {
            zn = conj(zn);
        }
        unhj(zn, gnu, 1, tol, &phi, &arg, &zeta1, &zeta2, &asum, &bsum);
        cz = zeta2 - zeta1;
        aarg = cabs(arg);
    }
    if (kode == 2) { cz -= zb; }
    if (ikflg == 2) { cz = -cz; }
    aphi = cabs(phi);
    rcz = creal(cz);

    /*  OVERFLOW TEST  */
    if (rcz > elim) { return -1; }
    if (rcz >= alim) {
        rcz += log(aphi);
        if (iform == 2) { rcz -= 0.25*log(aarg) + aic; }
        if (rcz > elim) { return -1; }
    } else {
        /*  UNDERFLOW TEST  */
        if (rcz >= -elim) {
            if (rcz > -alim) {
                /* pass */
            } else {
                rcz += log(aphi);
                if (iform == 2) { rcz -= 0.25*log(aarg) + aic; }
                if (rcz > -elim) {
                    /* goto 30 */
                    ascle = 1e3*d1mach[0] / tol;
                    cz += clog(phi);
                    if (iform != 1) { cz -= 0.25*log(arg) + aic;}
                    ax = exp(rcz) / tol;
                    ay = cimag(cz);
                    cz = ax*(cos(ay)+sin(ay)*I);
                    if (uchk(cz, ascle, tol)) {
                        for (int i = 0; i < nn; i++){ y[i] = 0.; }
                        return nn;
                    }
                } else {
                    for (int i = 0; i < nn; i++){ y[i] = 0.; }
                    return nn;
                }
            }
        } else {
            for (int i = 0; i < nn; i++){ y[i] = 0.; }
            return nn;
        }
    }
    if ((ikflg == 2) || (n == 1)) { return nuf; }
    /* 140 */
    while (1) {
        gnu = fnu + (nn -1);
        if (iform != 2) {
            init = 0;
            unik(zr, gnu, ikflg, 1, tol, &init, &phi, &zeta1, &zeta2, &sum, &cwrk[0]);
            cz = zeta2 - zeta1;
        } else {
            unhj(zn, gnu, 1, tol, &phi, &arg, &zeta1, &zeta2, &asum, &bsum);
            cz = zeta2 - zeta1;
            aarg = cabs(phi);
        }
        if (kode == 2) { cz -= zb; }

        /* 170 */
        aphi = cabs(phi);
        rcz = creal(cz);

        if (rcz >= -elim) {
            if (rcz > -alim) { return nuf; }
            rcz += log(aphi);
            if (iform == 2) { rcz -= 0.25*log(aarg) + aic; }
            if (rcz > -elim) {
                ascle = 1e3 * d1mach[0] / tol;
                cz = clog(phi);
                if (iform != 1) { cz -= 0.25*clog(arg) + aic; }
                ax = exp(rcz)/tol;
                ay = cimag(cz);
                cz = ax*(cos(ay)+sin(ay*I));
                if (!(uchk(cz, ascle, tol))) { return nuf; }
            }
        }

        y[nn-1] = 0.;
        nn -= 1;
        nuf += 1;
        if (nn == 0) { return nuf; }
    }
    return -1;
}
