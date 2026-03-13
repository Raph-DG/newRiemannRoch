import Mathlib

/-!
# Codimension Lemmas

Here we list various lemmas on codimension that we will need, culminating
in a proof that the codimension of a point is the same as the krull dimension
of its local ring.

Note: Of course, this will not be its own file in mathlib, but these lemmas
will be distributed across enough files that it's more convenient for this
repo to have them all in one file.

A more sensible placement for these lemmas is in the following PR: #26735.
-/

open Order

section OrderKrullDimension

variable {α β : Type*}

variable [Preorder α] [Preorder β]

lemma height_eq_of_strictMono (f : α → β) (hf : StrictMono f) (a : α)
    (h : ∀ p : LTSeries β, p.last = f a → ∃ p' :
    LTSeries α, p'.last = a ∧ p = p'.map f hf) : height a = height (f a) := by
  apply le_antisymm <|
    Order.height_le_height_apply_of_strictMono _ hf _
  refine height_le_iff'.mpr (fun p hp ↦ ?_)
  obtain ⟨p', hp'⟩ := h p hp
  rw [hp'.2, LTSeries.map_length p' f hf, (Order.height_eq_iSup_last_eq a)]
  have := le_iSup (α := ℕ∞) (fun p ↦ ⨆ (_ : RelSeries.last p = a), p.length) p'
  rwa [(ciSup_pos hp'.1 : (⨆ (_ : RelSeries.last p' = a), p'.length : ℕ∞) = p'.length)] at this

lemma coheight_eq_of_strictMono (f : α → β) (hf : StrictMono f) (a : α)
    (h : ∀ p : LTSeries β, p.head = f a → ∃ p' :
    LTSeries α, p'.head = a ∧ p = p'.map f hf) : coheight a = coheight (f a) := by
  apply le_antisymm <|
    Order.coheight_le_coheight_apply_of_strictMono _ hf _
  refine coheight_le_iff'.mpr (fun p hp ↦ ?_)
  obtain ⟨p', hp'⟩ := h p hp
  rw [hp'.2, LTSeries.map_length p' f hf, (Order.coheight_eq_iSup_head_eq a)]
  have := le_iSup (α := ℕ∞) (fun p ↦ ⨆ (_ : RelSeries.head p = a), p.length) p'
  rwa [(ciSup_pos hp'.1 : (⨆ (_ : RelSeries.head p' = a), p'.length : ℕ∞) = p'.length)] at this

end OrderKrullDimension

section Closeds

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

open TopologicalSpace IrreducibleCloseds Set Topology

lemma map_preimage_nonemtpy (f : β → α) (h : Continuous f) (T : IrreducibleCloseds β) :
    (f ⁻¹' (map f h T)).Nonempty :=
  (Nonempty.mono (closure_subset_preimage_closure_image h (s := T))
      (closure_nonempty_iff.mpr T.2.nonempty))

lemma IsPreirreducible.closure_image_preimage (f : β → α) (h : IsOpenMap f) (s : Set α)
    (hne : (f ⁻¹' s).Nonempty) (hs : IsPreirreducible s) (hs' : IsClosed s) :
    closure (f '' (f ⁻¹' s)) = s := by
  refine subset_antisymm (closure_minimal (by simp) hs') ?_
  refine subset_trans (subset_closure_inter_of_isPreirreducible_of_isOpen hs h.isOpen_range ?_) ?_
  · exact Set.nonempty_of_nonempty_preimage (f := f) (by simpa)
  · gcongr
    grind

lemma IsOpenMap.preimage_closure_image (f : β → α) (h₁ : IsOpenMap f)
    (h₂ : Function.Injective f) (h₃ : Continuous f) (s : Set β)
    (hs' : IsClosed s) :
    f ⁻¹' closure (f '' s) = s := by
  rw [h₁.preimage_closure_eq_closure_preimage h₃, Set.preimage_image_eq _ h₂, hs'.closure_eq]

/--
Given `f : U → X` a continuous open embedding, the irreducble closeds of `U` are order isomorphic
to the irreducible closeds of `X` nontrivially intersecting the range of `f`.
-/
noncomputable
def mapOrderIso (f : β → α) (h : IsOpenEmbedding f) :
    IrreducibleCloseds β ≃o {V : IrreducibleCloseds α | (f ⁻¹' V).Nonempty} where
  toFun T := ⟨map f h.continuous T, map_preimage_nonemtpy f h.continuous T⟩
  invFun V := {
      carrier := f ⁻¹' V
      isIrreducible' := ⟨V.2, IsPreirreducible.preimage (IsIrreducible.isPreirreducible V.1.2) h⟩
      isClosed' := V.1.3.preimage h.continuous
      }
  left_inv := by
    intro V
    simp only [map]
    ext x
    dsimp
    rw [IsOpenMap.preimage_closure_image f h.isOpenMap h.injective h.continuous]
    exact isClosed V
  right_inv := by
    intro V
    simp only [map]
    ext x
    dsimp
    rw [IsPreirreducible.closure_image_preimage f h.isOpenMap V V.2 V.1.2.2 V.1.3]
  map_rel_iff' := by
    intro a b
    simp only [coe_setOf, mem_setOf_eq]
    constructor
    · intro c
      have eq : f ⁻¹' closure (f '' a.carrier) ≤ f ⁻¹' closure (f '' b.carrier) := fun _ b ↦ c b
      have (z : IrreducibleCloseds β) : z.carrier = f ⁻¹' (closure (f '' z.carrier)) := by
        suffices closure z.carrier = f ⁻¹' (closure (f '' z.carrier)) by
          nth_rewrite 1 [← IsClosed.closure_eq z.3]
          exact this
        exact Topology.IsEmbedding.closure_eq_preimage_closure_image h.isEmbedding z
      rwa [← this a, ← this b] at eq
    · exact fun c ↦ (map_mono h.continuous) c

end Closeds

section TopologicalKrullDimension

variable {α : Type*} [TopologicalSpace α]

open TopologicalSpace Topology Order Set IrreducibleCloseds

lemma Topology.IsOpenEmbedding.coheight_map {U X : Type*} [TopologicalSpace U]
    [TopologicalSpace X] {f : U → X} (hf : IsOpenEmbedding f)
    (Z : TopologicalSpace.IrreducibleCloseds U) :
    Order.coheight (map f hf.continuous Z) = Order.coheight Z := by
  rw [← coheight_orderIso (mapOrderIso f hf) Z]
  let g : {V : IrreducibleCloseds X | (f ⁻¹' ↑V).Nonempty} ↪o
      IrreducibleCloseds X :=
    OrderEmbedding.subtype {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty}
  let a := (mapOrderIso f hf) Z
  have : ∀ p : LTSeries (IrreducibleCloseds X), p.head = g a →
         ∃ p' : LTSeries ({V : IrreducibleCloseds X | (f ⁻¹' ↑V).Nonempty}),
           p'.head = a ∧ p = p'.map g (OrderEmbedding.strictMono g) := fun p hp ↦ by
    let p' : LTSeries {V : IrreducibleCloseds X | (f ⁻¹' ↑V).Nonempty} := {
      length := p.length
      toFun i := {
        val := p i
        property := by
          suffices  ¬ f ⁻¹' a = ∅ by
            rw[← Ne, ← nonempty_iff_ne_empty] at this
            exact Nonempty.mono (fun _ b ↦ (hp ▸ LTSeries.head_le p i) b) this
          exact nonempty_iff_ne_empty.mp a.2
      }
      step := p.step
    }
    exact ⟨p', SetCoe.ext hp, rfl⟩
  exact (coheight_eq_of_strictMono g (fun _ _ a ↦ a)
     ((mapOrderIso f hf) Z) this).symm

attribute [local instance] specializationOrder

@[simp]
lemma coe_irreducibleEquivPoints_symm_apply [QuasiSober α] [T0Space α] (x : α) :
    (irreducibleSetEquivPoints.symm x : Set α) = closure {x} := rfl

lemma Topology.IsOpenEmbedding.coheight_eq {U X : Type*} [TopologicalSpace U] [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [QuasiSober U] [T0Space U]
    {x : U} (f : U → X) (hf : IsOpenEmbedding f) :
    coheight (f x) = coheight x := by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm (f x),
    ← coheight_orderIso (irreducibleSetEquivPoints (α := U)).symm x,
    ← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]

end TopologicalKrullDimension

open TopologicalSpace Set AlgebraicGeometry Topology CategoryTheory

namespace AlgebraicGeometry

open IrreducibleCloseds in
@[stacks 02I4]
lemma coheight_eq_of_isOpenImmersion {U X : Scheme} {x : U} (f : U ⟶ X)
    [IsOpenImmersion f] : Order.coheight (f.base x) = Order.coheight x :=
  f.isOpenEmbedding.coheight_eq

lemma primeSpectrum_preorder_eq_orderDual_spec_preorder (R : CommRingCat) :
    PrimeSpectrum.instPartialOrder.toPreorder = OrderDual.instPreorder ↥(Spec R) := by
  ext
  simp only [PrimeSpectrum.le_iff_specializes]
  exact Eq.to_iff rfl

open Order in
lemma ideal_height_eq_coheight (R : CommRingCat) (x : Spec R) :
    x.asIdeal.height = coheight x := by
  rw [Ideal.height_eq_primeHeight x.asIdeal, Ideal.primeHeight]
  congr
  exact primeSpectrum_preorder_eq_orderDual_spec_preorder R

open Order in
@[stacks 02IZ]
lemma ringKrullDim_stalk_eq_coheight {X : Scheme} (x : X) :
  ringKrullDim (X.presheaf.stalk x) = Order.coheight x := by
  wlog h : ∃ R, X = Spec R
  · obtain ⟨R, f, hf, hsub⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
      (show x ∈ ⊤ from trivial)
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hsub.1
    rw [coheight_eq_of_isOpenImmersion, ← this _ ⟨R, rfl⟩]
    exact Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.comapEquiv (asIso (Scheme.Hom.stalkMap f y)).commRingCatIsoToRingEquiv)
  obtain ⟨R, rfl⟩ := h
  let k : Algebra ↑R ↑((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra (↑R) x
  have : IsLocalization.AtPrime (↑((Spec R).presheaf.stalk x)) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal ((Spec R).presheaf.stalk x)]
  apply WithBot.coe_eq_coe.mpr
  exact ideal_height_eq_coheight R x
