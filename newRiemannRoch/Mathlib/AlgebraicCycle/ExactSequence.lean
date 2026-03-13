import Mathlib
import newRiemannRoch.Mathlib.AlgebraicCycle.Sheaf
import newRiemannRoch.Mathlib.OrderOfVanishing.Noetherian

set_option backward.isDefEq.respectTransparency false

/-!
# Twisted closed subscheme exact sequence

In this file we define the following exact sequence on a curve:
`0 → 𝒪ₓ(D - P) → 𝒪ₓ(D) → k(P) → 0` where `k(P)` is the skyscraper
at `P` for some closed point `P`.

Currently this file is a work in progress - sheaves of modules are a little bit hellish to work
with in a concrete way at the moment.
-/
universe u

open Function.locallyFinsuppWithin

open AlgebraicGeometry AlgebraicCycle Sheaf Opposite Order

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (p : X)

namespace AlgebraicCycle
namespace Sheaf

/-
If `f` is a section of `𝒪ₓ(D)`, then it is also a section of `𝒪ₓ(D + D')` for effective `D'`.
-/
lemma extend_prop {D D' : AlgebraicCycle X ℤ} (h : D' ≥ 0) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    {f : X.functionField} (hf : f ∈ carrier D U.unop) : f ∈ carrier (D + D') U.unop := by
  simp [carrier] at hf ⊢
  intro fnez
  specialize hf fnez
  constructor
  · exact hf.1
  intro hx
  apply le_trans hf.2
  simp
  intro z
  simp [restrict_apply]
  split_ifs
  · simpa using h z
  · rfl

variable [IsRegularInCodimensionOne X]
/--
The inclusion mapping `𝒪ₓ(D) ⟶ 𝒪ₓ(D + D')`, defined by `h ↦ h`.
-/
noncomputable
def extend (D D' : AlgebraicCycle X ℤ) (h : D' ≥ 0) :
    sheafOfModules D ⟶ sheafOfModules (D + D') where
  val := {
    app U :=
      ModuleCat.ofHom
        {
          toFun := fun ⟨f, hf⟩ ↦ ⟨f, extend_prop h U hf⟩
          map_add' := by aesop
          map_smul' :=
            /-
            I think this should be by aesop again once the definition
            of smul is fixed
            -/
            sorry --by aesop; sorry
        }
  }

open CategoryTheory

/--
The inclusion morphism `𝒪ₓ(D) ⟶ 𝒪ₓ(D + D')` is a monomorphism
-/
lemma extend_mono (D D' : AlgebraicCycle X ℤ) (h : D' ≥ 0) :
    Mono <| extend D D' h := by
  suffices ∀ (U : (TopologicalSpace.Opens ↥X)ᵒᵖ), Function.Injective <|
    (extend D D' h).val.app U by
    suffices Mono <| (SheafOfModules.toSheaf X.ringCatSheaf).map <|
      extend D D' h by cat_disch
    exact
      Sheaf.mono_of_injective
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (extend D D' h)) this
  intro U
  simp [extend]
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  change (AddHom.toFun _) (⟨x, hx⟩ : ↑((sheafOfModules D).val.obj U)) =
         (AddHom.toFun _) (⟨y, hy⟩ : ↑((sheafOfModules D).val.obj U)) at h
  --change (ModuleCat.ofHom _) _ = (ModuleCat.ofHom _) _ at h

  simp [-AddHom.toFun_eq_coe, -LinearMap.toFun_eq_coe] at h
  --change (fun (x : ↑(carrier D (unop U))) ↦ ⟨↑x, extend._proof_1 D D' U ↑x⟩) ⟨x, hx⟩ = (fun x ↦ ⟨↑x, _⟩) ⟨y, hy⟩ at h
  /-
  grind used to work here, not quite sure what changed...
  TODO: Make this compile again
  -/
  sorry
  --grind

open Classical in
def _root_.AlgebraicCycle.single_apply {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (c : ℤ) (z : X) :
    single x c z = if z = x then c else 0 := by
  unfold single
  change Set.indicator {x} (Function.const X c) z = _
  simp [Set.indicator_apply]

omit [IsRegularInCodimensionOne X] in
/--
A cycle supported at a single point with a positive coefficient is effective.
-/
lemma _root_.AlgebraicCycle.single_effective (x : X) (c : ℤ) (hc : c ≥ 0) : single x c ≥ 0 := by
  intro z
  simp [single_apply x c z]
  by_cases o : x = z
  all_goals grind


variable (D : AlgebraicCycle X ℤ)
/--
On open sets away from a point `P`, `extend` is surjective (and hence bijective, and hence
an isomorphism of modules)
-/
lemma extend_surjective (U : X.Opensᵒᵖ) (hU : p ∉ U.1):
    Function.Surjective <| ((extend (D - single p 1) (single p 1)
    (single_effective p 1 (by simp))).val.app U).hom := by sorry

open Classical in
/--
This definition is a bit of a placeholder - it will almost certainly become inlined at some point,
it's mainly just here to make porting easier
-/
noncomputable
def skyscraperAb : TopCat.Sheaf Ab X := skyscraperSheaf p (.of <| X.residueField p)

noncomputable
instance instModuleResidueField (U : X.Opens) (hP : p ∈ U) :
  Module ↑(X.ringCatSheaf.obj.obj (op U)) ↑(X.residueField p) :=
  (X.evaluation U p hP).hom.toModule

def module_pos_of_ab {P : Prop} (R : Type*) (M N : AddCommGrpCat) [CommRing R]
    [Decidable P] (h : P) [m : Module R M] :
    Module R (AddCommGrpCat.carrier (if P then M else N)) := by
  have : (if P then M else N) = M := if_pos h
  convert m
  congr

def module_neg_of_ab {P : Prop} (R : Type*) (M N : AddCommGrpCat) [CommRing R]
    [Decidable P] (h : ¬P) [m : Module R N] :
    Module R (AddCommGrpCat.carrier (if P then M else N)) := by
  have : (if P then M else N) = N := if_neg h
  convert m
  congr

noncomputable
instance : Unique ((⊤_ Ab).carrier : Type u) := by
  suffices Unique (ToType (⊤_ Ab.{u})) by
    exact this
  infer_instance

noncomputable
instance {R : Type u} [CommRing R] : Module R (ToType (⊤_ Ab.{u})) where
  smul a b := b
  mul_smul a b c := rfl
  one_smul a := rfl
  smul_zero a := rfl
  smul_add a b c := rfl
  add_smul a b c := by apply Subsingleton.elim
  zero_smul a := by apply Subsingleton.elim

instance {R : Type*} [CommRing R] {a : Type*} [AddCommMonoid a] [Unique a] :
    Unique (Module R a) := by
  constructor
  intro a
  · ext a b
    apply Subsingleton.elim
  · constructor
    exact {
      smul a b := b
      mul_smul a b c := rfl
      one_smul a := rfl
      smul_zero a := rfl
      smul_add a b c := rfl
      add_smul a b c := by apply Subsingleton.elim
      zero_smul a := by apply Subsingleton.elim
    }

open Classical in
noncomputable
instance (U : (TopologicalSpace.Opens X)ᵒᵖ) : Module ↑(X.ringCatSheaf.obj.obj U)
  ↑((skyscraperAb p).presheaf.obj U) := by
  simp [skyscraperAb, skyscraperSheaf, skyscraperPresheaf]
  by_cases o : p ∈ unop U
  · suffices Module ↑(X.sheaf.obj.obj U) (AddCommGrpCat.of <| X.residueField p) from
      module_pos_of_ab (X.sheaf.obj.obj U) ((AddCommGrpCat.of ↑(X.residueField p))) (⊤_ Ab) o
    exact instModuleResidueField p (unop U) o
  · exact module_neg_of_ab (X.sheaf.obj.obj U) ((AddCommGrpCat.of ↑(X.residueField p))) (⊤_ Ab) o



noncomputable
def skyscraperPresheafOfModules : PresheafOfModules X.ringCatSheaf.obj := by
  apply PresheafOfModules.ofPresheaf (skyscraperAb p).presheaf

  intro U V k s s'
  simp [skyscraperAb, skyscraperSheaf]

  sorry

noncomputable
def skyscraperSheafOfModules : SheafOfModules X.ringCatSheaf where
  val := skyscraperPresheafOfModules p
  isSheaf := (skyscraperAb p).2

/--
Map from `𝒪ₓ(D)` to the skyscraper sheaf at a point `p` on an open set U.
-/
noncomputable
def toSkyscraperFun {U : X.Opens}
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (s : (sheafOfModules D).val.obj (op U)) :
    ↑((skyscraperAb p).presheaf.obj (op U)) := by
  by_cases hs : s.1 = 0
  · exact 0
  by_cases o : p ∈ U
  · simp only [skyscraperAb, skyscraperSheaf, skyscraperPresheaf, o, ↓reduceIte]
    have : IsDiscreteValuationRing (X.presheaf.stalk p) := by
      /-
      TODO: Copy API for IsRegularInCodimensionOne over from the normal schemes
      branch
      -/
      sorry
    choose n u hn using IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ s.1 hs
    exact X.residue p (u * ϖ ^ (n + D p).toNat)
  · simp only [skyscraperAb, skyscraperSheaf, skyscraperPresheaf, o, ↓reduceIte]
    exact default

noncomputable
def toSkyscraper (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
    sheafOfModules D ⟶ skyscraperSheafOfModules p where
  val := {
    app U := by
      apply ModuleCat.ofHom (X := D.sheafOfModules.val.obj U)
        (Y := (skyscraperSheafOfModules p).val.obj U)
      apply LinearMap.mk
      · -- TODO: Make this its own lemma (i.e. show toSkyscraperFun is a homomorphism).
        sorry
      · apply AddHom.mk
        · sorry
        · exact toSkyscraperFun p D ϖ hϖ hp
  }

instance (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (hD : ∀ z : X, coheight z ≠ 1 → D z ≥ 0)
    (pClosed : ∀ x : X, x ≤ p → x = p) :
    CategoryTheory.Sheaf.IsLocallySurjective <|
    (SheafOfModules.toSheaf X.ringCatSheaf).map <| toSkyscraper p D ϖ hϖ hp := by sorry

noncomputable
def twistedClosedSubschemeComplex (ϖ : X.presheaf.stalk p)
    (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
  ShortComplex X.Modules where
  X₁ := sheafOfModules (D - single p 1)
  X₂ := sheafOfModules D
  X₃ := skyscraperSheafOfModules p
  f :=
    /-
    This is a somewhat questionable definition tbh. I don't love that we need this rewrite here,
    and I think it could be worthwhile making a version of the lineBundleMapping which
    explicitly uses D - P -> D
    -/
    let k := extend (D - single p 1) (single p 1) (by sorry)
    have : sheafOfModules (D - single p 1 + single p 1) = sheafOfModules D := by simp
    this ▸ k

  g := toSkyscraper p D ϖ hϖ hp
  zero :=
    /-
    Once we have this stated properly this will follow more or less trivially by the following
    little argument.

    Proof:
    h = u ϖ^n where n ≥ 1 - D P

    g (h) = res (u ϖ ^(n + D P))
          = res (u ϖ ^ m ), m ≥ 1,
          = 0
    -/
    sorry

/-
This should be no work at all with the above definitons (at least that's the hope).
-/
lemma twistedClosedSubschemeComplex_exact (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ)
    (hp : coheight p = 1)
    (PClosed : ∀ x : X, x ≤ p → x = p) : (twistedClosedSubschemeComplex p D ϖ hϖ hp).Exact := sorry

end Sheaf
end AlgebraicCycle
