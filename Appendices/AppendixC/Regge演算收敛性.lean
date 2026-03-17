theorem regge_convergence (K : CellComplex) (χ : ℕ → CellComplex) 
    (h_refine : ∀ n, refines (χ n) K) (h_limit : Hausdorff_limit χ K) (Λ : ℝ) :
    Tendsto (fun n => Regge_action (χ n) Λ) atTop 
      (𝓝 (∫ x in (K : Manifold), (R x - 2 * Λ) ∂volume))