have h_prod_ne_zero : ∏ i, amplitude (getOp (gs i)) ≠ 0 :=
  prod_ne_zero_of_unitary (λ i => amplitude (getOp (gs i))) 
    (λ i => unitary_on_operad (getOp (gs i)))