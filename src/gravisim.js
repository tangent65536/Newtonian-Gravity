/**
 * Copyright (c) 2021, tan2pow16. All rights reserved.
 */

'use strict';

class MassObj
{
  constructor(x0, y0, u0, v0, _radi, _density)
  {
    this.id = 0; // Unique id
    this.idx = 0; // For recursive collision check

    this.x = [x0, 0, 0, 0, 0];
    this.y = [y0, 0, 0, 0, 0];
    this.u = [u0, 0, 0, 0, 0];
    this.v = [v0, 0, 0, 0, 0];
    this.radi = _radi;
    this.mass = _density * _radi * _radi; // Use r^2 for 2D simu.

    this.colli = -1;
  }

  getX()
  {
    return this.x[0];
  }

  getY()
  {
    return this.y[0];
  }

  getU()
  {
    return this.u[0];
  }

  getV()
  {
    return this.v[0];
  }
}

class GravSimulator
{
  static #XI = +0.1786178958448091E+00;
  static #LAMBDA = -0.2123418310626054E+00;
  static #CHI = -0.6626458266981849E-01;

  // Softening parameter squared. Set to 0 to get default behavior.
  #eps2;

  // Constants for PEFRL position integral evaluations.
  #constRs;

  // Constants for PEFRL velocity integral evaluations.
  #constVs;

  // Anchor-dependent param for faster calculations (less 'if' operations).
  #anchorStartIndex;

  constructor(_masses, _anchor, _colli, _g, _dt, _eps)
  {
    this.masses = _masses;
    this.doAnchor = _anchor;
    this.doColli = _colli;
    this.constG = _g;
    this.dt = _dt;
    this.#eps2 = _eps ? _eps * _eps : 0;

    if(this.doAnchor)
    {
      for(let i = 1 ; i <= 4 ; i++)
      {
        this.masses[0].x[i] = this.masses[0].x[0];
        this.masses[0].y[i] = this.masses[0].y[0];
      }
    }

    this.#constRs = [GravSimulator.#XI * this.dt,
                     GravSimulator.#CHI * this.dt,
                     (1 - 2 * (GravSimulator.#CHI + GravSimulator.#XI)) * this.dt,
                     GravSimulator.#CHI * this.dt,
                     GravSimulator.#XI * this.dt
                    ];

    this.#constVs = [(0.5 - GravSimulator.#LAMBDA) * this.dt,
                     GravSimulator.#LAMBDA * this.dt,
                     GravSimulator.#LAMBDA * this.dt,
                     (0.5 - GravSimulator.#LAMBDA) * this.dt
                    ];

    this.#anchorStartIndex = (this.doAnchor ? 1 : 0);

    this.energy = 0;
    let dx, dy, dLen
    for(let i = 0 ; i < this.masses.length ; i++)
    {
      this.masses[i].id = i;
      this.energy += 0.5 * this.masses[i].mass * (this.masses[i].u[0] * this.masses[i].u[0] + this.masses[i].v[0] * this.masses[i].v[0]);
      for(let j = 0 ; j < i ; j++)
      {
        dx = this.masses[i].x - this.masses[j].x;
        dy = this.masses[i].y - this.masses[j].y;

        dLen = Math.sqrt(dx * dx + dy * dy);

        this.energy -= this.constG * this.masses[i].mass * this.masses[j].mass / dLen;
      }
    }
  }

  #collisionTestErg(mass1, mass2)
  {
    let dx, dy, dLen2, dLen, sRad, sRad2, i, j, k, l, dxi, dyi, dxk, dyk, dxik, dyik, dxki, dyki;

    dx = mass1.x[0] - mass2.x[0];
    dy = mass1.y[0] - mass2.y[0];

    dLen2 = dx * dx + dy * dy;

    dLen = Math.sqrt(dLen2);
    this.energy -= this.constG * mass1.mass * mass2.mass / dLen;
    
    sRad = mass1.radi + mass2.radi;
    sRad2 = sRad * sRad;

    if(dLen2 <= sRad2)
    {
      return true;
    }

    for(i = 1 ; i <= 4 ; i++)
    {
      j = i % 4 + 1;

      dxi = mass1.x[j] - mass1.x[i];
      dyi = mass1.y[j] - mass1.y[i];
      for(k = 1 ; k <= 4 ; k++)
      {
        l = k % 4 + 1;

        dxik = mass2.x[k] - mass1.x[i];
        dyik = mass2.y[k] - mass1.y[i];

        dxki = mass2.x[l] - mass1.x[i];
        dyki = mass2.y[l] - mass1.y[i];

        if((dxi * dyik - dyi * dxik) * (dxi * dyki - dyi * dxki) <= 0)
        {
          dxk = mass2.x[l] - mass2.x[k];
          dyk = mass2.y[l] - mass2.y[k];

          dxki = mass1.x[j] - mass2.x[k];
          dyki = mass1.y[j] - mass2.y[k];

          // The cross product of dk x dik is now negative as we didn't reverse the sign of d*ik vector;
          if((dxk * dyik - dyk * dxik) * (dxk * dyki - dyk * dxki) >= 0)
          {
            return true;
          }
        }
      }
    }

    return false;
  }

  static #collisionTest(mass1, mass2)
  {
    let dx, dy, dLen2, sRad, sRad2, i, j, k, l, dxi, dyi, dxk, dyk, dxik, dyik, dxki, dyki;

    dx = mass1.x[0] - mass2.x[0];
    dy = mass1.y[0] - mass2.y[0];

    dLen2 = dx * dx + dy * dy;
    
    sRad = mass1.radi + mass2.radi;
    sRad2 = sRad * sRad;

    if(dLen2 <= sRad2)
    {
      return true;
    }

    dx = Math.abs(mass1.x[1] - mass1.x[3]) + mass1.radi + Math.abs(mass1.x[1] - mass1.x[3]) + mass2.radi;
    dy = Math.abs(mass1.y[1] - mass1.y[3]) + mass1.radi + Math.abs(mass1.y[1] - mass1.y[3]) + mass2.radi;

    // Distance between 2 objects is significantly greater than available travel distance;
    if(dx * dx + dy * dy < dLen2)
    {
      return false;
    }

    for(i = 1 ; i <= 4 ; i++)
    {
      j = i % 4 + 1;

      dxi = mass1.x[j] - mass1.x[i];
      dyi = mass1.y[j] - mass1.y[i];
      for(k = 1 ; k <= 4 ; k++)
      {
        l = k % 4 + 1;

        dxik = mass2.x[k] - mass1.x[i];
        dyik = mass2.y[k] - mass1.y[i];

        dxki = mass2.x[l] - mass1.x[i];
        dyki = mass2.y[l] - mass1.y[i];

        if((dxi * dyik - dyi * dxik) * (dxi * dyki - dyi * dxki) <= 0)
        {
          dxk = mass2.x[l] - mass2.x[k];
          dyk = mass2.y[l] - mass2.y[k];

          dxki = mass1.x[j] - mass2.x[k];
          dyki = mass1.y[j] - mass2.y[k];

          // The cross product of dk x dik is now negative as we didn't reverse the sign of d*ik vector;
          if((dxk * dyik - dyk * dxik) * (dxk * dyki - dyk * dxki) >= 0)
          {
            return true;
          }
        }
      }
    }

    return false;
  }

  #handleCollisions()
  {
    let i, collidx, masscmb;

    for(i = this.#anchorStartIndex ; i < this.masses.length ; i++)
    {
      if(this.masses[i].mass > 0 && this.masses[i].colli >= 0)
      {
        collidx = this.masses[i].colli;
        while(collidx >= 0 && this.masses[collidx].mass <= 0)
        {
          collidx = this.masses[collidx].colli;
        }

        masscmb = this.masses[collidx].mass + this.masses[i].mass;
        if(collidx >= this.#anchorStartIndex)
        {
          this.masses[collidx].x[0] = (this.masses[collidx].x[0] * this.masses[collidx].mass + this.masses[i].x[0] * this.masses[i].mass) / masscmb;
          this.masses[collidx].y[0] = (this.masses[collidx].y[0] * this.masses[collidx].mass + this.masses[i].y[0] * this.masses[i].mass) / masscmb;
          this.masses[collidx].u[0] = (this.masses[collidx].u[0] * this.masses[collidx].mass + this.masses[i].u[0] * this.masses[i].mass) / masscmb;
          this.masses[collidx].v[0] = (this.masses[collidx].v[0] * this.masses[collidx].mass + this.masses[i].v[0] * this.masses[i].mass) / masscmb;
        }
        this.masses[collidx].mass = masscmb;

        this.masses[collidx].radi = Math.sqrt(this.masses[collidx].radi * this.masses[collidx].radi + this.masses[i].radi * this.masses[i].radi);

        this.masses[i].mass = -1;
      }
    }

    for(i = this.#anchorStartIndex ; i < this.masses.length ; i++)
    {
      if(this.masses[i].colli >= 0)
      {
        if(this.masses[i].mass > 0)
        {
          console.error(`Collision merging error for mass obj at [${i}]!`);
        }
        else
        {
          this.masses.splice(i, 1);
          i--;
        }
      }
      else
      {
        this.masses[i].idx = i;
      }
    }
  }

  step()
  {
    let dx, dy, dLen, dLen2, dLen2ov3inv, ax_, ay_, i, i_1, j, k;
    for(i = 1 ; i <= 4 ; i++)
    {
      i_1 = i - 1;

      for(j = this.#anchorStartIndex ; j < this.masses.length ; j++)
      {
        this.masses[j].x[i] = this.masses[j].x[i_1] + this.masses[j].u[i_1] * this.#constRs[i_1];
        this.masses[j].y[i] = this.masses[j].y[i_1] + this.masses[j].v[i_1] * this.#constRs[i_1];
        this.masses[j].u[i] = this.masses[j].u[i_1];
        this.masses[j].v[i] = this.masses[j].v[i_1];
      }

      for(j = this.#anchorStartIndex ; j < this.masses.length ; j++)
      {
        for(k = 0 ; k < j ; k++)
        {
          dx = this.masses[j].x[i] - this.masses[k].x[i];
          dy = this.masses[j].y[i] - this.masses[k].y[i];

          dLen2 = dx * dx + dy * dy;
          dLen = Math.sqrt(dLen2);

          // The extra '#eps2' here is to mitigate the singularity when distance between 2 objects is close to 0.
          dLen2ov3inv = 1 / ((dLen2 + this.#eps2) * dLen);

          ax_ = this.constG * dx * dLen2ov3inv * this.#constVs[i_1];
          ay_ = this.constG * dy * dLen2ov3inv * this.#constVs[i_1];

          this.masses[j].u[i] -= ax_ * this.masses[k].mass;
          this.masses[j].v[i] -= ay_ * this.masses[k].mass;

          this.masses[k].u[i] += ax_ * this.masses[j].mass;
          this.masses[k].v[i] += ay_ * this.masses[j].mass;
        }
      }
    }

    for(i = this.#anchorStartIndex ; i < this.masses.length ; i++)
    {
      // Previous positions;
      this.masses[i].x[1] = this.masses[i].x[0];
      this.masses[i].y[1] = this.masses[i].y[0];

      // Integral step results;
      this.masses[i].x[0] = this.masses[i].x[4] + this.masses[i].u[4] * this.#constRs[4];
      this.masses[i].y[0] = this.masses[i].y[4] + this.masses[i].v[4] * this.#constRs[4];
      this.masses[i].u[0] = this.masses[i].u[4];
      this.masses[i].v[0] = this.masses[i].v[4];

      // Swiped rectangle nodes;
      dx = this.masses[i].x[0] - this.masses[i].x[1];
      dy = this.masses[i].y[0] - this.masses[i].y[1];
      dLen = this.masses[i].radi / Math.sqrt(dx * dx + dy * dy);

      // Norm vector in length of radius;
      ax_ = -dy * dLen;
      ay_ = dy * dLen;

      // All 4 points.
      this.masses[i].x[4] = this.masses[i].x[1] + ax_;
      this.masses[i].y[4] = this.masses[i].y[1] + ay_;

      this.masses[i].x[3] = this.masses[i].x[1] - ax_;
      this.masses[i].y[3] = this.masses[i].y[1] - ay_;

      this.masses[i].x[2] = this.masses[i].x[0] + ax_;
      this.masses[i].y[2] = this.masses[i].y[0] + ay_;

      this.masses[i].x[1] = this.masses[i].x[0] - ax_;
      this.masses[i].y[1] = this.masses[i].y[0] - ay_;
    }

    this.energy = 0;
    if(this.doColli)
    {
      let collist0 = [], collist1 = [];
      for(i = this.#anchorStartIndex ; i < this.masses.length ; i++)
      {
        this.energy += 0.5 * this.masses[i].mass * (this.masses[i].u[0] * this.masses[i].u[0] + this.masses[i].v[0] * this.masses[i].v[0]);

        for(j = 0 ; j < i ; j++)
        {
          if(this.#collisionTestErg(this.masses[i], this.masses[j]))
          {
            if(j < this.#anchorStartIndex || this.masses[j].mass >= this.masses[i].mass)
            {
              this.masses[i].colli = j;
              collist0.push(this.masses[j]);
            }
            else
            {
              this.masses[j].colli = i;
              collist0.push(this.masses[i]);
            }
          }
        }
      }

      this.#handleCollisions();

      while(collist0.length > 0)
      {
        for(i = 0 ; i < collist0.length ; i++)
        {
          for(j = 0 ; j < this.masses.length ; j++)
          {
            if(collist0[i].idx === j)
            {
              continue;
            }
  
            if(GravSimulator.#collisionTest(collist0[i], this.masses[j]))
            {
              if(j < this.#anchorStartIndex || this.masses[j].mass >= collist0[i].mass)
              {
                collist0[i].colli = j;
                collist1.push(this.masses[j]);
              }
              else
              {
                this.masses[j].colli = collist0[i].idx;
                collist1.push(collist0[i]);
              }
            }
          }
        }

        this.#handleCollisions();

        collist0 = collist1;
        collist1 = [];
      }
    }
    else
    {
      for(i = 0 ; i < this.masses.length ; i++)
      {
        this.energy += 0.5 * this.masses[i].mass * (this.masses[i].u[0] * this.masses[i].u[0] + this.masses[i].v[0] * this.masses[i].v[0]);
        for(j = 0 ; j < i ; j++)
        {
          dx = this.masses[i].x - this.masses[j].x;
          dy = this.masses[i].y - this.masses[j].y;

          dLen = Math.sqrt(dx * dx + dy * dy);

          this.energy -= this.g * this.masses[i].mass * this.masses[j].mass / dLen;
        }
      }
    }

    // console.log(this.energy);
  }
}
