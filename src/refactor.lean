import linear_algebra.bilinear_form

universes u v w

variables {R : Type u} [comm_ring R] {M₁ : Type v} {M₂ : Type w}
variables [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]
variables {K : Type v} [field K] {V₁ : Type u} {V₂ : Type w}
variables [add_comm_group V₁] [vector_space K V₁] [add_comm_group V₂] [vector_space K V₂]
variables [finite_dimensional K V₁] [finite_dimensional K V₂]

open module

namespace submodule

-- lemma le_double_dual_annihilator_comap_eval (U : submodule R M₁) : 
--   U ≤ U.dual_annihilator.dual_annihilator.comap (dual.eval R M₁) :=
-- begin
--   intros x hx,
--   simp_rw [submodule.mem_comap, submodule.mem_dual_annihilator],
--   intros φ hφ,
--   exact hφ _ hx,
-- end

end submodule

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

section finite_dimensional

open finite_dimensional bilin_form

-- lemma submodule.double_dual_annihilator_findim_eq (U : subspace K V₁) :
--   findim K U.dual_annihilator.dual_annihilator = findim K U :=
-- begin
--   zify,
--   let D := U.dual_annihilator.dual_annihilator,
--   suffices : (findim K V₁ : ℤ) - findim K D = findim K V₁ - findim K U,
--     linarith,
--   symmetry,
--   rw ← (subspace.quot_equiv_annihilator U.dual_annihilator).findim_eq,
--   conv_lhs { rw ← submodule.findim_quotient_add_findim U },
--   conv_rhs { rw [← subspace.dual_findim_eq, 
--                  ← submodule.findim_quotient_add_findim U.dual_annihilator] },
--   rw (subspace.quot_equiv_annihilator U).findim_eq,
--   simp,
-- end

-- lemma submodule.double_dual_annihilator_findim_eq_comap_eval (U : subspace K V₁) :
--   findim K (U.dual_annihilator.dual_annihilator.comap (dual.eval K V₁)) = 
--   findim K U :=
-- begin
--   conv_rhs { rw ← submodule.double_dual_annihilator_findim_eq },
--   rw [show dual.eval K V₁ = vector_space.eval_equiv.to_linear_map, by refl],
--   exact linear_equiv.findim_eq (linear_equiv.comap _ _),
-- end

-- lemma submodule.eq_double_dual_annihilator_comap_eval (U : submodule K V₁) : 
--   U = U.dual_annihilator.dual_annihilator.comap (dual.eval K V₁) :=
-- eq_of_le_of_findim_eq U.le_double_dual_annihilator_comap_eval 
--   U.double_dual_annihilator_findim_eq_comap_eval.symm

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
  rwa [bilin_form.restrict_apply, submodule.coe_mk, submodule.coe_mk, hB] at hB₁
end

lemma bilin_form.to_lin_restrict_ker_eq_inf_orthogonal
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

noncomputable def f (p : subspace K V₁) (q : subspace K p) :
  q ≃ₗ[K] q.map p.subtype :=
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

lemma baz' (p : subspace K V₁) (q : subspace K p) :
  findim K (q.map p.subtype) = findim K q :=
linear_equiv.findim_eq (f p q).symm

lemma baz (B : bilin_form K V₁) (W : subspace K V₁) (hB : sym_bilin_form.is_sym B) :
  findim K ((B.to_lin.dom_restrict W).ker.map W.subtype) =
  findim K (B.to_lin.dom_restrict W).ker := baz' _ _

def foo (Φ : submodule R (module.dual R M₁)) : submodule R M₁ :=
Φ.dual_annihilator.comap (dual.eval R M₁)

lemma mem_foo_iff {Φ : submodule R (module.dual R M₁)} (x : M₁) :
  x ∈ foo Φ ↔ ∀ φ : Φ, φ x = 0 := 
begin
  simp_rw [foo, submodule.mem_comap, submodule.mem_dual_annihilator],
  split; intros h φ,
  { exact h φ.1 φ.2 },
  { intro hφ, exact h ⟨φ, hφ⟩ }
end

lemma to_lin_restrict_range_eq_dual_annihilator
  (B : bilin_form K V₁) (W : subspace K V₁) (hB : sym_bilin_form.is_sym B) :
  foo (B.to_lin.dom_restrict W).range = B.orthogonal W :=
begin
  ext x, split; rw [mem_orthogonal_iff]; intro hx,
  { intros y hy,
    rw mem_foo_iff at hx,
    refine hx ⟨B.to_lin.dom_restrict W ⟨y, hy⟩, ⟨y, hy⟩, _, rfl⟩,
    simp only [submodule.top_coe] },
  { rw mem_foo_iff,
    rintro ⟨_, ⟨w, hw⟩, _, rfl⟩,
    exact hx w hw }
end

-- @[simps apply]
-- def foo_to_dual_annihilator (Φ : subspace K (module.dual K V₁)) :
--   foo Φ →ₗ[K] Φ.dual_annihilator :=
-- { to_fun := λ x,
--   ⟨{ to_fun := λ φ, φ x.1,
--      map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.add_apply],
--      map_smul' := by simp only [forall_const, linear_map.smul_apply, eq_self_iff_true]},
--      begin
--        rw submodule.mem_dual_annihilator,
--        intros φ hφ,
--        exact ((mem_foo_iff _).1 x.2) ⟨φ, hφ⟩,
--      end⟩,
--   map_add' :=
--     begin
--       rintro _ _,
--       ext φ,
--       exact φ.map_add _ _,
--     end,
--   map_smul' :=
--     begin
--       rintro _ _,
--       ext φ,
--       exact φ.map_smul _ _,
--     end }

-- lemma eq_of_dual_apply_eq (x y : V₁)
--   (h : ∀ φ : module.dual K V₁, φ x = φ y) : x = y :=
-- begin
--   classical,
--   obtain ⟨b, hb⟩ := exists_is_basis K V₁,
--   have : ∀ i : b, hb.to_dual _ i x = hb.to_dual _ i y,
--   { intro _, rw h },
--   simp_rw is_basis.to_dual_apply_right at this,
--   exact is_basis.ext_elem hb this,
-- end

-- def foo_eq_dual_annihilator_comap {Φ : submodule R (dual R M₁)} : 
--   foo Φ = Φ.dual_annihilator.comap (dual.eval R M₁) :=
-- begin
--   ext x, 
--   simp_rw [mem_foo_iff, submodule.mem_comap, submodule.mem_dual_annihilator],
--   split; intros hx φ,
--   { intro hφ,
--     exact hx ⟨φ, hφ⟩ },
--   { exact hx φ.1 φ.2 }
-- end

lemma kopj {Φ : submodule K (dual K V₁)} :
  findim K (foo Φ) = findim K Φ.dual_annihilator :=
begin
  rw [foo, show dual.eval K V₁ = vector_space.eval_equiv.to_linear_map, by refl],
  apply linear_equiv.findim_eq,
  apply linear_equiv.comap,
end

lemma barz (W : subspace K (module.dual K V₁)) :
  findim K W + findim K (foo W) = findim K V₁ :=
begin
  rw [kopj, W.quot_equiv_annihilator.findim_eq.symm, add_comm, 
      submodule.findim_quotient_add_findim, subspace.dual_findim_eq],
end

lemma findim_add_findim_orthogonal
  {B : bilin_form K V₁} {W : subspace K V₁} (hB₁ : sym_bilin_form.is_sym B) :
  findim K W + findim K (B.orthogonal W) =
  findim K V₁ + findim K (W ⊓ B.orthogonal ⊤ : subspace K V₁) :=
begin
  rw [← bilin_form.to_lin_restrict_ker_eq_inf_orthogonal _ _ hB₁,
      ← to_lin_restrict_range_eq_dual_annihilator _ _ hB₁, 
      ← barz (B.to_lin.dom_restrict W).range, baz _ _ hB₁],
  conv_rhs { rw [add_comm, ← add_assoc, add_comm (findim K ↥((B.to_lin.dom_restrict W).ker)),
                 linear_map.findim_range_add_findim_ker] },
end

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

end finite_dimensional