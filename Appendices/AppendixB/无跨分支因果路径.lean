theorem no_cross_branch_causal_path
    (f : Operation A args c)
    (gs : ∀ i, Σ _ _, Operation A _ _)
    (h_res : ∀ i, (gs i).2.1 = [args.get i])
    (i j : Fin args.length) (hij : i ≠ j)
    (x : A.M) (hx : x ∈ relsOfOp (getOp (gs i)))
    (y : A.M) (hy : y ∈ relsOfOp (getOp (gs j))) :
    ¬ B.lt x y ∧ ¬ B.lt y x :=