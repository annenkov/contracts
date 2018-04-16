-- Generic pricing
-- ==
-- compiled input @ OptionPricing-data/medium.in
-- output @ OptionPricing-data/medium.out

import "/futlib/math"
import "/futlib/array"
import "Price"

module Payoff1 =
{
let payoffInternal(ext : [][]f32, tenv : []i32, disc : []f32, t0 : i32, t_now : i32): f32 =
  (if ((!(((if ((((if ((((((ext[0+ t0,0])) - (3758.05f32))) < ((((ext[0+ t0,1])) - (11840.0f32)))))then ((((ext[0+ t0,0])) - (3758.05f32)))else ((((ext[0+ t0,1])) - (11840.0f32))))) < ((((ext[0+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[0+ t0,0])) - (3758.05f32))) < ((((ext[0+ t0,1])) - (11840.0f32)))))then ((((ext[0+ t0,0])) - (3758.05f32)))else ((((ext[0+ t0,1])) - (11840.0f32)))))else ((((ext[0+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1150.0f32) * (disc[0+ t0])))else ((if ((!(((if ((((if ((((((ext[1+ t0,0])) - (3758.05f32))) < ((((ext[1+ t0,1])) - (11840.0f32)))))then ((((ext[1+ t0,0])) - (3758.05f32)))else ((((ext[1+ t0,1])) - (11840.0f32))))) < ((((ext[1+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[1+ t0,0])) - (3758.05f32))) < ((((ext[1+ t0,1])) - (11840.0f32)))))then ((((ext[1+ t0,0])) - (3758.05f32)))else ((((ext[1+ t0,1])) - (11840.0f32)))))else ((((ext[1+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1300.0f32) * (disc[1+ t0])))else ((if ((!(((if ((((if ((((((ext[2+ t0,0])) - (3758.05f32))) < ((((ext[2+ t0,1])) - (11840.0f32)))))then ((((ext[2+ t0,0])) - (3758.05f32)))else ((((ext[2+ t0,1])) - (11840.0f32))))) < ((((ext[2+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[2+ t0,0])) - (3758.05f32))) < ((((ext[2+ t0,1])) - (11840.0f32)))))then ((((ext[2+ t0,0])) - (3758.05f32)))else ((((ext[2+ t0,1])) - (11840.0f32)))))else ((((ext[2+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1450.0f32) * (disc[2+ t0])))else ((if ((!(((if ((((if ((((((ext[3+ t0,0])) - (3758.05f32))) < ((((ext[3+ t0,1])) - (11840.0f32)))))then ((((ext[3+ t0,0])) - (3758.05f32)))else ((((ext[3+ t0,1])) - (11840.0f32))))) < ((((ext[3+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[3+ t0,0])) - (3758.05f32))) < ((((ext[3+ t0,1])) - (11840.0f32)))))then ((((ext[3+ t0,0])) - (3758.05f32)))else ((((ext[3+ t0,1])) - (11840.0f32)))))else ((((ext[3+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1600.0f32) * (disc[3+ t0])))else ((if ((!(((if ((((if ((((((ext[4+ t0,0])) - (3758.05f32))) < ((((ext[4+ t0,1])) - (11840.0f32)))))then ((((ext[4+ t0,0])) - (3758.05f32)))else ((((ext[4+ t0,1])) - (11840.0f32))))) < ((((ext[4+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[4+ t0,0])) - (3758.05f32))) < ((((ext[4+ t0,1])) - (11840.0f32)))))then ((((ext[4+ t0,0])) - (3758.05f32)))else ((((ext[4+ t0,1])) - (11840.0f32)))))else ((((ext[4+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1750.0f32) * (disc[4+ t0])))else ((if ((!(((((((ext[4+ t0,0])) < (((0.75f32) * (3758.05f32))))) || ((((ext[4+ t0,1])) < (((0.75f32) * (11840.0f32))))))) || ((((ext[4+ t0,2])) < (((0.75f32) * (1200.0f32))))))))then (((1000.0f32) * (disc[4+ t0])))else (((((1000.0f32) * ((if ((((if ((((((ext[4+ t0,0])) / (3758.05f32))) < ((((ext[4+ t0,1])) / (11840.0f32)))))then ((((ext[4+ t0,0])) / (3758.05f32)))else ((((ext[4+ t0,1])) / (11840.0f32))))) < ((((ext[4+ t0,2])) / (1200.0f32)))))then ((if ((((((ext[4+ t0,0])) / (3758.05f32))) < ((((ext[4+ t0,1])) / (11840.0f32)))))then ((((ext[4+ t0,0])) / (3758.05f32)))else ((((ext[4+ t0,1])) / (11840.0f32)))))else ((((ext[4+ t0,2])) / (1200.0f32))))))) * (disc[4+ t0]))))))))))))))
let payoffFun(ext : [][]f32, tenv : []i32, disc : []f32, t_now : i32): f32 = payoffInternal(ext, tenv, disc, 0, t_now)

let payoff disc _ ext = payoffFun(ext, [], disc, 0)
}

-- after cutPayoff
module Payoff2 =
{
let payoffInternal(ext : [][]f32, tenv : []i32, disc : []f32, t0 : i32, t_now : i32): f32 =
  (if ((!(((if ((((if ((((((ext[0+ t0,0])) - (3758.05f32))) < ((((ext[0+ t0,1])) - (11840.0f32)))))then ((((ext[0+ t0,0])) - (3758.05f32)))else ((((ext[0+ t0,1])) - (11840.0f32))))) < ((((ext[0+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[0+ t0,0])) - (3758.05f32))) < ((((ext[0+ t0,1])) - (11840.0f32)))))then ((((ext[0+ t0,0])) - (3758.05f32)))else ((((ext[0+ t0,1])) - (11840.0f32)))))else ((((ext[0+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1150.0f32) * ((if ((((0) + t0) < (t_now)))then (0.0f32)else (disc[0+ t0])))))else ((if ((!(((if ((((if ((((((ext[1+ t0,0])) - (3758.05f32))) < ((((ext[1+ t0,1])) - (11840.0f32)))))then ((((ext[1+ t0,0])) - (3758.05f32)))else ((((ext[1+ t0,1])) - (11840.0f32))))) < ((((ext[1+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[1+ t0,0])) - (3758.05f32))) < ((((ext[1+ t0,1])) - (11840.0f32)))))then ((((ext[1+ t0,0])) - (3758.05f32)))else ((((ext[1+ t0,1])) - (11840.0f32)))))else ((((ext[1+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1300.0f32) * ((if ((((1) + t0) < (t_now)))then (0.0f32)else (disc[1+ t0])))))else ((if ((!(((if ((((if ((((((ext[2+ t0,0])) - (3758.05f32))) < ((((ext[2+ t0,1])) - (11840.0f32)))))then ((((ext[2+ t0,0])) - (3758.05f32)))else ((((ext[2+ t0,1])) - (11840.0f32))))) < ((((ext[2+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[2+ t0,0])) - (3758.05f32))) < ((((ext[2+ t0,1])) - (11840.0f32)))))then ((((ext[2+ t0,0])) - (3758.05f32)))else ((((ext[2+ t0,1])) - (11840.0f32)))))else ((((ext[2+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1450.0f32) * ((if ((((2) + t0) < (t_now)))then (0.0f32)else (disc[2+ t0])))))else ((if ((!(((if ((((if ((((((ext[3+ t0,0])) - (3758.05f32))) < ((((ext[3+ t0,1])) - (11840.0f32)))))then ((((ext[3+ t0,0])) - (3758.05f32)))else ((((ext[3+ t0,1])) - (11840.0f32))))) < ((((ext[3+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[3+ t0,0])) - (3758.05f32))) < ((((ext[3+ t0,1])) - (11840.0f32)))))then ((((ext[3+ t0,0])) - (3758.05f32)))else ((((ext[3+ t0,1])) - (11840.0f32)))))else ((((ext[3+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1600.0f32) * ((if ((((3) + t0) < (t_now)))then (0.0f32)else (disc[3+ t0])))))else ((if ((!(((if ((((if ((((((ext[4+ t0,0])) - (3758.05f32))) < ((((ext[4+ t0,1])) - (11840.0f32)))))then ((((ext[4+ t0,0])) - (3758.05f32)))else ((((ext[4+ t0,1])) - (11840.0f32))))) < ((((ext[4+ t0,2])) - (1200.0f32)))))then ((if ((((((ext[4+ t0,0])) - (3758.05f32))) < ((((ext[4+ t0,1])) - (11840.0f32)))))then ((((ext[4+ t0,0])) - (3758.05f32)))else ((((ext[4+ t0,1])) - (11840.0f32)))))else ((((ext[4+ t0,2])) - (1200.0f32))))) < (0.0f32))))then (((1750.0f32) * ((if ((((4) + t0) < (t_now)))then (0.0f32)else (disc[4+ t0])))))else ((if ((!(((((((ext[4+ t0,0])) < (((0.75f32) * (3758.05f32))))) || ((((ext[4+ t0,1])) < (((0.75f32) * (11840.0f32))))))) || ((((ext[4+ t0,2])) < (((0.75f32) * (1200.0f32))))))))then (((1000.0f32) * ((if ((((4) + t0) < (t_now)))then (0.0f32)else (disc[4+ t0])))))else (((((1000.0f32) * ((if ((((if ((((((ext[4+ t0,0])) / (3758.05f32))) < ((((ext[4+ t0,1])) / (11840.0f32)))))then ((((ext[4+ t0,0])) / (3758.05f32)))else ((((ext[4+ t0,1])) / (11840.0f32))))) < ((((ext[4+ t0,2])) / (1200.0f32)))))then ((if ((((((ext[4+ t0,0])) / (3758.05f32))) < ((((ext[4+ t0,1])) / (11840.0f32)))))then ((((ext[4+ t0,0])) / (3758.05f32)))else ((((ext[4+ t0,1])) / (11840.0f32)))))else ((((ext[4+ t0,2])) / (1200.0f32))))))) * ((if ((((4) + t0) < (t_now)))then (0.0f32)else (disc[4+ t0]))))))))))))))))
let payoffFun(ext : [][]f32, tenv : []i32, disc : []f32, t_now : i32): f32 = payoffInternal(ext, tenv, disc, 0, t_now)

let payoff disc _ ext = payoffFun(ext, [], disc, 0)
}

module P1 = Price Payoff1
module P2 = Price Payoff2

-- Entry point
let main [num_bits][num_models][num_und][num_dates]
        (contract_number: i32,
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
