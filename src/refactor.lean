import linear_algebra.bilinear_form

universes u v w

variables {R : Type u} [comm_ring R] {M₁ : Type v} {M₂ : Type w}
variables [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]
variables {K : Type v} [field K] {V₁ : Type u} {V₂ : Type w}
variables [add_comm_group V₁] [vector_space K V₁] [add_comm_group V₂] [vector_space K V₂]
variables [finite_dimensional K V₁] [finite_dimensional K V₂]

open module

/-- Given `f : M₁ ≃ₗ[R] M₂` and `U` a submodule of `M₂`, `f.comap U` is the 
induced `linear_equiv` from `U.comap f.to_linear_map` to `U`. -/
def linear_equiv.comap (f : M₁ ≃ₗ[R] M₂) (U : submodule R M₂) :
  U.comap f.to_linear_map ≃ₗ[R] U :=
f.of_submodules _ _ 
begin 
  ext x, 
  simp_rw [submodule.mem_map, submodule.mem_comap],
  split; intro hx,
  { rcases hx with ⟨y, hy, rfl⟩,
    exact hy },
  { refine ⟨f.inv_fun x, _⟩,
    simpa }
end

/-- Given `p` a submodule of the module `M` and `q` a submodule of `p`, `p.equiv_subtype_map q` 
is the natural `linear_equiv` between `q` and `q.map p.subtype`. -/
noncomputable def submodule.equiv_subtype_map 
  (p : submodule R M₁) (q : submodule R p) : q ≃ₗ[R] q.map p.subtype :=
linear_equiv.of_bijective ((p.subtype.dom_restrict q).cod_restrict _
  begin
    rintro ⟨x, hx⟩,
    refine ⟨x, hx, rfl⟩,
  end)
  begin
    rw linear_map.ker_eq_bot,
    rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ hxy,
    rw [subtype.mk_eq_mk, subtype.mk_eq_mk],
    injections with hxy,
  end
  begin
    rw linear_map.range_eq_top,
    rintro ⟨x, hx⟩,
    rcases hx with ⟨y, hy, rfl⟩,
    refine ⟨⟨y, hy⟩, rfl⟩,
  end

lemma finite_dimensional.subtype_eq_findim_eq (p : subspace K V₁) (q : subspace K p) :
  finite_dimensional.findim K (q.map p.subtype) = finite_dimensional.findim K q :=
linear_equiv.findim_eq (p.equiv_subtype_map q).symm

/-- The pullback of a submodule in the dual space along the evaluation map. -/
def submodule.dual_annihilator_comap (Φ : submodule R (module.dual R M₁)) : submodule R M₁ :=
Φ.dual_annihilator.comap (dual.eval R M₁)

lemma submodule.mem_dual_annihilator_comap_iff {Φ : submodule R (module.dual R M₁)} (x : M₁) :
  x ∈ Φ.dual_annihilator_comap ↔ ∀ φ : Φ, φ x = 0 := 
begin
  simp_rw [submodule.dual_annihilator_comap, submodule.mem_comap, 
           submodule.mem_dual_annihilator],
  split; intros h φ,
  { exact h φ.1 φ.2 },
  { intro hφ, exact h ⟨φ, hφ⟩ }
end

lemma submodule.dual_annihilator_comp_findim_eq {Φ : submodule K (dual K V₁)} :
  finite_dimensional.findim K Φ.dual_annihilator_comap = 
  finite_dimensional.findim K Φ.dual_annihilator :=
begin
  rw [submodule.dual_annihilator_comap, 
      show dual.eval K V₁ = vector_space.eval_equiv.to_linear_map, by refl],
  apply linear_equiv.findim_eq,
  apply linear_equiv.comap,
end

lemma submodule.findim_add_findim_dual_annihilator_comap_eq 
  (W : subspace K (module.dual K V₁)) : finite_dimensional.findim K W + 
  finite_dimensional.findim K W.dual_annihilator_comap = finite_dimensional.findim K V₁ :=
begin
  rw [submodule.dual_annihilator_comp_findim_eq, 
      W.quot_equiv_annihilator.findim_eq.symm, add_comm,
      submodule.findim_quotient_add_findim, subspace.dual_findim_eq],
end

namespace bilin_form

section finite_dimensional

open finite_dimensional bilin_form

/-- The restriction of a nondegenerate bilinear form `B` onto a submodule `W` is 
nondegenerate if `W ⊓ B.orthogonal W ≤ ⊥`. -/
lemma nondegenerate_restrict_of_inf_orthogonal_le_bot
  (B : bilin_form R M₁) (hB : sym_bilin_form.is_sym B)
  {W : submodule R M₁} (hW : W ⊓ B.orthogonal W ≤ ⊥) :
  (B.restrict W).nondegenerate :=
begin
  rintro ⟨x, hx⟩ hB₁,
  rw [submodule.mk_eq_zero, ← submodule.mem_bot R],
  refine hW ⟨hx, λ y hy, _⟩,
  specialize hB₁ ⟨y, hy⟩,
  rwa [restrict_apply, submodule.coe_mk, submodule.coe_mk, hB] at hB₁
end

lemma to_lin_restrict_ker_eq_inf_orthogonal
  (B : bilin_form K V₁) (W : subspace K V₁) (hB : sym_bilin_form.is_sym B) :
  (B.to_lin.dom_restrict W).ker.map W.subtype = (W ⊓ B.orthogonal ⊤ : subspace K V₁) :=
begin
  ext x, split; intro hx,
  { rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩,
    erw linear_map.mem_ker at hker,
    split,
    { simp [hx] },
    { intros y _,
      rw [is_ortho, hB],
      change (B.to_lin.dom_restrict W) ⟨x, hx⟩ y = 0,
      rw hker, refl } },
  { simp_rw [submodule.mem_map, linear_map.mem_ker],
    refine ⟨⟨x, hx.1⟩, _, rfl⟩,
    ext y, change B x y = 0,
    rw hB,
    exact hx.2 _ submodule.mem_top }
end

lemma to_lin_restrict_range_eq_dual_annihilator
  (B : bilin_form K V₁) (W : subspace K V₁) (hB : sym_bilin_form.is_sym B) :
  (B.to_lin.dom_restrict W).range.dual_annihilator_comap = B.orthogonal W :=
begin
  ext x, split; rw [mem_orthogonal_iff]; intro hx,
  { intros y hy,
    rw submodule.mem_dual_annihilator_comap_iff at hx,
    refine hx ⟨B.to_lin.dom_restrict W ⟨y, hy⟩, ⟨y, hy⟩, _, rfl⟩,
    simp only [submodule.top_coe] },
  { rw submodule.mem_dual_annihilator_comap_iff,
    rintro ⟨_, ⟨w, hw⟩, _, rfl⟩,
    exact hx w hw }
end

lemma findim_add_findim_orthogonal
  {B : bilin_form K V₁} {W : subspace K V₁} (hB₁ : sym_bilin_form.is_sym B) :
  findim K W + findim K (B.orthogonal W) =
  findim K V₁ + findim K (W ⊓ B.orthogonal ⊤ : subspace K V₁) :=
begin
  rw [← to_lin_restrict_ker_eq_inf_orthogonal _ _ hB₁,
      ← to_lin_restrict_range_eq_dual_annihilator _ _ hB₁, 
      ← (B.to_lin.dom_restrict W).range.findim_add_findim_dual_annihilator_comap_eq, 
      subtype_eq_findim_eq],
  conv_rhs { rw [add_comm, ← add_assoc, add_comm (findim K ↥((B.to_lin.dom_restrict W).ker)),
                 linear_map.findim_range_add_findim_ker] },
end

/-- A subspace is complement to its orthogonal complement with respect to some 
bilinear form if that bilinear form restricted on to the subspace is nondegenerate. -/
lemma restrict_nondegenerate_of_is_compl_orthogonal
  {B : bilin_form K V₁} {W : subspace K V₁}
  (hB₁ : sym_bilin_form.is_sym B) (hB₂ : (B.restrict W).nondegenerate) :
  is_compl W (B.orthogonal W) :=
begin
  have : W ⊓ B.orthogonal W = ⊥,
  { rw eq_bot_iff,
    intros x hx,
    obtain ⟨hx₁, hx₂⟩ := submodule.mem_inf.1 hx,
    refine subtype.mk_eq_mk.1 (hB₂ ⟨x, hx₁⟩ _),
    rintro ⟨n, hn⟩,
    rw [restrict_apply, submodule.coe_mk, submodule.coe_mk, hB₁],
    exact hx₂ n hn },
  refine ⟨this ▸ le_refl _, _⟩,
  { rw top_le_iff,
    refine finite_dimensional.eq_top_of_findim_eq _,
    refine le_antisymm (submodule.findim_le _) _,
    conv_rhs { rw ← add_zero (findim K _) },
    rw [← findim_bot K V₁, ← this, submodule.dim_sup_add_dim_inf_eq,
        findim_add_findim_orthogonal hB₁],
    exact nat.le.intro rfl }
end

/-- A subspace is complement to its orthogonal complement with respect to some bilinear form 
if and only if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_iff_is_compl_orthogonal
  {B : bilin_form K V₁} {W : subspace K V₁} (hB₁ : sym_bilin_form.is_sym B) : 
  (B.restrict W).nondegenerate ↔ is_compl W (B.orthogonal W) :=
⟨ λ hB₂, restrict_nondegenerate_of_is_compl_orthogonal hB₁ hB₂, 
  λ h, B.nondegenerate_restrict_of_inf_orthogonal_le_bot hB₁ h.1⟩

end finite_dimensional

end bilin_form