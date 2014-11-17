#include "../includeC/Constants.h"

#ifdef VECT_KERNEL
    #define underlyings(i,j)   \
        (inst_traj[(i*num_under + j)<<lgWARP])
#else
    #define underlyings(i,j)   \
        (inst_traj[i*num_under + j])
#endif

inline
void trajectory_inner(
        const       UINT    num_cash_flows, // number of discounts
        const       UINT    model_ind,      // the model index
        const       UINT    disct_index,    // index of the discount 
        const       REAL    amount,         // update with amount
        __constant REAL*    md_discts,  
        __local    REAL*    local_vhat
) {
    UINT index = model_ind * get_local_size(0); //block_size;
    local_vhat[index] += ( amount * md_discts[model_ind*num_cash_flows+disct_index] );
}

// Small Dataset Contract Definition
inline 
void payoffFunction( // SIMPLE
        const      UINT     model_num,  // the index of the current model
        const      UINT     num_under,  // the number of underlyings
        const      UINT     num_cash_flows, // the number of discounts
        const      UINT     num_pricers,// the number of deterministic procers 
        __constant REAL*    md_discts,  // [num_models][num_cash_flows] discounts
        __constant REAL*    md_detvals, // [num_models, num_det_pricers]  pricers 
#ifdef VECT_KERNEL
        __global   REAL*    inst_traj,
#else
        const      REAL*    inst_traj,  // [num_dates, num_under] current trajectory
#endif
        __local    REAL*    vhat        // [model_num] Accumulated per-model price        
) {

{|CODE|}

}

