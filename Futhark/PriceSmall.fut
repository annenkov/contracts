-- Generic pricing
-- ==
-- compiled input @ OptionPricing-data/small.in
-- output @ OptionPricing-data/small.out

import "/futlib/math"
import "/futlib/array"
import "Price"

default(f32)

let trajInner(amount: f32, ind: i32, disc: []f32): f32 = amount * unsafe disc[ind]

let payoff1(md_disct: []f32, md_detval: []f32, xss: [1][1]f32): f32 =
  let detval = unsafe md_detval[0]
  let amount = ( xss[0,0] - 4000.0 ) * detval
  let amount0= if (0.0 < amount) then amount else 0.0
  in  trajInner(amount0, 0, md_disct)

module Payoff1 = { let payoff x y z = payoff1(x, y, z) }

module P1 = Price Payoff1

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
  in if contract_number == 1 then P1.price r
     else []
