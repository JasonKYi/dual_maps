import linear_algebra.bilinear_form

universes u v w

variables {R : Type u} [comm_ring R] {M₁ : Type v} {M₂ : Type w}
variables [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]

namespace linear_map

open module

def dual_map (f : M₁ →ₗ[R] M₂) : dual R M₂ →ₗ[R] dual R M₁ :=
lcomp R R f

@[simp] lemma dual_map_apply (f : M₁ →ₗ[R] M₂) (g : dual R M₂) (x : M₁) :
  f.dual_map g x = g (f x) := 
lcomp_apply f g x

variable {f : M₁ →ₗ[R] M₂}

lemma ker_dual_map_eq_range_dual_annihilator : 
  f.dual_map.ker = f.range.dual_annihilator :=
begin
  ext φ, split; intro hφ,
  { rw mem_ker at hφ,
    rw submodule.mem_dual_annihilator,
    rintro y ⟨x, _, rfl⟩,
    rw [← dual_map_apply, hφ], 
    refl },
  { ext x,
    rw dual_map_apply,
    rw submodule.mem_dual_annihilator at hφ,
    exact hφ (f x) ⟨x, 
      show x ∈ (⊤ : submodule R M₁), by exact submodule.mem_top, rfl⟩ }
end

lemma range_dual_map_le_dual_annihilator_ker :
  f.dual_map.range ≤ f.ker.dual_annihilator :=
begin
  rintro _ ⟨ψ, _, rfl⟩,
  simp_rw [submodule.mem_dual_annihilator, mem_ker],
  rintro x hx,
  rw [dual_map_apply, hx, map_zero]
end

section finite_dimensional

variables {K : Type v} [field K] {V₁ : Type u} {V₂ : Type w}
variables [add_comm_group V₁] [vector_space K V₁] [add_comm_group V₂] [vector_space K V₂]
variables [finite_dimensional K V₁] [finite_dimensional K V₂]

open finite_dimensional

lemma findim_range_dual_map_eq_findim_range {f : V₁ →ₗ[K] V₂} : 
  findim K f.dual_map.range = findim K f.range :=
begin
  have := submodule.findim_quotient_add_findim f.range,
  rw [(subspace.quot_equiv_annihilator f.range).findim_eq, 
      ← ker_dual_map_eq_range_dual_annihilator] at this,
  conv_rhs at this { rw ← subspace.dual_findim_eq },
  refine add_left_injective (findim K f.dual_map.ker) _,
  change _ + _ = _ + _,
  rw [findim_range_add_findim_ker f.dual_map, add_comm, this],
end

lemma range_dual_map_eq_dual_annihilator_ker {f : V₁ →ₗ[K] V₂} :
  f.dual_map.range = f.ker.dual_annihilator :=
begin
  refine eq_of_le_of_findim_eq range_dual_map_le_dual_annihilator_ker _,
  have := submodule.findim_quotient_add_findim f.ker,
  rw (subspace.quot_equiv_annihilator f.ker).findim_eq at this,
  refine add_left_injective (findim K f.ker) _,
  simp_rw [this, findim_range_dual_map_eq_findim_range],
  exact findim_range_add_findim_ker f,
end

end finite_dimensional

end linear_map

namespace submodule

variables {U V : submodule R M₁}

lemma dual_annihilator_sup_eq_inf_dual_annihilator :
  (U ⊔ V).dual_annihilator = U.dual_annihilator ⊓ V.dual_annihilator :=
begin
  ext φ,
  rw [mem_inf, mem_dual_annihilator, mem_dual_annihilator, mem_dual_annihilator],
  split; intro h,
  { refine ⟨_, _⟩;
    intros x hx,
    refine h x (mem_sup.2 ⟨x, hx, 0, zero_mem _, add_zero _⟩),
    refine h x (mem_sup.2 ⟨0, zero_mem _, x, hx, zero_add _⟩) },
  { simp_rw mem_sup,
    rintro _ ⟨x, hx, y, hy, rfl⟩,
    rw [linear_map.map_add, h.1 _ hx, h.2 _ hy, add_zero] }
end

end submodule