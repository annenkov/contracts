-- Generic pricing
-- ==
-- compiled input @ OptionPricing-data/large.in
-- output @ OptionPricing-data/large.out

import "/futlib/math"
import "/futlib/array"
import "Price"

default(f32)

let trajInner(amount: f32, ind: i32, disc: []f32): f32 = amount * unsafe disc[ind]

let fminPayoff(xs: []f32): f32 =
  --    MIN( map(/, xss, {3758.05, 11840.0, 1200.0}) )
  let (a,b,c) = ( xs[0]/3758.05, xs[1]/11840.0, xs[2]/1200.0)
  in if a < b
     then if a < c then a else c
     else if b < c then b else c

let payoff3(md_disct: []f32, xss: [367][3]f32): f32 =
  let conds  = map (\x ->
                      x[0] <= 2630.6349999999998 ||
                      x[1] <= 8288.0             ||
                      x[2] <=  840.0)
                   xss
  let cond  = or conds
  let price1= trajInner(100.0,  0, md_disct)
  let goto40= cond && ( xss[366,0] < 3758.05 ||
                        xss[366,1] < 11840.0 ||
                        xss[366,2] < 1200.0)
  let amount= if goto40
              then 1000.0 * fminPayoff(xss[366])
              else 1000.0
  let price2 = trajInner(amount, 1, md_disct)
  in price1 + price2

module Payoff3 = { let payoff x _ z = payoff3(x, z) }

module P3 = Price Payoff3

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
  in if contract_number == 3 then P3.price r
     else []
