-- Generic pricing
-- ==
-- compiled input @ OptionPricing-data/new1.in
-- output @ OptionPricing-data/new1.out

import "/futlib/math"
import "/futlib/array"
import "Price"

default(f32)

module Payoff1 = {

  let payoffInternal(ext : [][]f32, _tenv : []i32, disc : []f32, t0 : i32, _t_now : i32): f32 =
    unsafe
    (((if (((4000.0) < ((ext[1+ t0,0])))) then
             ((((((ext[1+ t0,0])) - (4000.0))) * (disc[1+ t0])))
       else (0.0))) +
     ((if (((3000.0) < ((ext[0+ t0,1])))) then
             ((((((ext[0+ t0,1])) - (3000.0))) * (disc[0+ t0])))
       else (0.0))))

  let payoffFun(ext : [][]f32, tenv : []i32, disc : []f32, t_now : i32): f32 =
    payoffInternal(ext, tenv, disc, 0, t_now)

 let payoff disc _ ext = payoffFun(ext, [], disc, 0)
}

module Payoff2 = {

  let payoffInternal(ext : [][]f32, _tenv : []i32, disc : []f32, t0 : i32, t_now : i32): f32 =
    unsafe
    (((if (((4000.0) < ((ext[1+ t0,0])))) then
          ((((((ext[1+ t0,0])) - (4000.0))) *
            ((if ((((1) + t0) < (t_now))) then (0.0)
              else (disc[1+ t0])))))
       else (0.0))) + ((if (((3000.0) < ((ext[0+ t0,1])))) then
          ((((((ext[0+ t0,1])) - (3000.0))) *
            ((if ((((0) + t0) < (t_now))) then (0.0)
              else (disc[0+ t0])))))else (0.0))))

  let payoffFun(ext : [][]f32, tenv : []i32, disc : []f32, t_now : i32): f32 =
    payoffInternal(ext, tenv, disc, 0, t_now)

 let payoff disc _ ext = payoffFun(ext, [], disc, 0)
}

module P1 = Price Payoff1
module P2 = Price Payoff2

-- Entry point
let main [num_bits][num_models][num_und][num_dates]
        (_contract_number: i32,
         num_mc_it: i32,
         dir_vs: [][num_bits]i32,
         md_cs: [num_models][num_und][num_und]f32,
         md_vols: [num_models][num_dates][num_und]f32,
         md_drifts: [num_models][num_dates][num_und]f32,
         md_sts: [num_models][num_und]f32,
         md_detvals: [num_models][]f32,
         md_discts: [num_models][]f32,
         bb_inds: [3][num_dates]i32,
         bb_data: [3][num_dates]f32)
         : []f32 =
  let r = {num_mc_it,dir_vs,md_cs,md_vols,md_drifts,md_sts,md_detvals,md_discts,bb_inds,bb_data}
  in if false then P1.price r
     else P2.price r
