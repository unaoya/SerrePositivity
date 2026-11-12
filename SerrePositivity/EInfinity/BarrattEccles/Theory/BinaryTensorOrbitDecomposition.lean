module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorOrbitInputs
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# 実際の二色入力表現の軌道直和

HA 3.2.4.7 の自由比較の入力を、固定 arity ごとに標準代表の安定化群からの
誘導表現へ分解する。直和の包含は指定された入力包含を誘導した射である。
任意の複体の全整数次数を扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
attribute [local instance] Classical.propDecidable
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A) (r : ℕ)

/-- 標準代表の安定化群からの誘導入力。 -/
def binaryTensorOrbitInduced (k : ULift.{u} (Fin (r + 1))) (i : ℤ) :=
  Rep.ind (binaryTensorPatternSubgroup r k).subtype ((binaryTensorOrbitInput X Y r k).X i)

/-- 標準代表の包含を誘導して得る、実際の入力の包含。 -/
def binaryTensorOrbitInducedInclusion (k : ULift.{u} (Fin (r + 1))) (i : ℤ) :
    binaryTensorOrbitInduced X Y r k i ⟶ (binaryTensorFullInput X Y r).X i :=
  finiteInductionInclusion (binaryTensorPatternSubgroup r k)
    ((binaryTensorOrbitInput X Y r k).X i) ((binaryTensorFullInput X Y r).X i)
    ((binaryTensorOrbitInputInclusion X Y r k).f i)

set_option maxHeartbeats 1600000 in
-- 誘導表現の指定生成元から実際のテンソル冪の各次数まで定義を展開する。
/-- 標準代表から誘導した包含は、実際の入力表現からの射を検出する。 -/
lemma binaryTensorOrbitInduced_hom_ext (i : ℤ)
    {Z : Rep.{u} A (ULift.{u} (Equiv.Perm (Fin r)))}
    (f g : (binaryTensorFullInput X Y r).X i ⟶ Z)
    (h : ∀ k, binaryTensorOrbitInducedInclusion X Y r k i ≫ f =
      binaryTensorOrbitInducedInclusion X Y r k i ≫ g) : f = g := by
  have hb (k : ULift.{u} (Fin (r + 1))) (x : (binaryTensorOrbitInput X Y r k).X i) :
      f.hom (((binaryTensorOrbitInputInclusion X Y r k).f i).hom x) =
        g.hom (((binaryTensorOrbitInputInclusion X Y r k).f i).hom x) := by
    let adj := Rep.indResAdjunction A (binaryTensorPatternSubgroup r k).subtype
    have he := congrArg (adj.homEquiv ((binaryTensorOrbitInput X Y r k).X i) Z) (h k)
    rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right] at he
    have hi : adj.homEquiv _ _ (binaryTensorOrbitInducedInclusion X Y r k i) =
        (binaryTensorOrbitInputInclusion X Y r k).f i :=
      (Rep.indResHomEquiv (binaryTensorPatternSubgroup r k).subtype _ _).apply_symm_apply _
    rw [hi] at he
    exact congrArg (fun φ => φ.hom x) he
  apply (forget₂ (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin r)))) (ModuleCat A)).map_injective
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (.up ℤ) i)
    (binaryTensorWordsIsColimit X Y r)).hom_ext
  intro j
  change (binaryTensorWordInclusion X Y r j.as).f i ≫ _ =
    (binaryTensorWordInclusion X Y r j.as).f i ≫ _
  obtain ⟨k, σ, hσ⟩ := binaryTensorCountPattern_covers r j.as
  let w := binaryTensorCountPattern r k
  let e : binaryTensorWordObj X Y r w ≅ binaryTensorWordObj X Y r j.as :=
    binaryTensorWordPermutationIso X Y r σ w ≪≫
      eqToIso (congrArg (binaryTensorWordObj X Y r) hσ)
  have he : e.hom ≫ binaryTensorWordInclusion X Y r j.as =
      binaryTensorWordInclusion X Y r w ≫ (permutationAction (X ⊞ Y) r σ).asIso.hom := by
    simp only [e, Iso.trans_hom, eqToIso.hom, Category.assoc]
    rw [binaryTensorWordInclusion_word_eq X Y hσ, binaryTensorWordPermutationIso_inclusion]
  apply (cancel_epi (e.hom.f i)).1
  rw [← Category.assoc, ← Category.assoc]
  change (e.hom ≫ binaryTensorWordInclusion X Y r j.as).f i ≫ _ =
    (e.hom ≫ binaryTensorWordInclusion X Y r j.as).f i ≫ _
  rw [he]
  ext x
  change f.hom (((binaryTensorFullInput X Y r).X i).ρ (ULift.up σ)
      (((binaryTensorOrbitInputInclusion X Y r (ULift.up k)).f i).hom x)) =
    g.hom (((binaryTensorFullInput X Y r).X i).ρ (ULift.up σ)
      (((binaryTensorOrbitInputInclusion X Y r (ULift.up k)).f i).hom x))
  rw [Rep.hom_comm_apply f, Rep.hom_comm_apply g, hb]

/-- 標準代表から誘導した実際の入力表現の指定双錐。 -/
def binaryTensorOrbitBicone (i : ℤ) :
    Bicone (fun k => binaryTensorOrbitInduced X Y r k i) :=
  finiteInductionBicone ((binaryTensorFullInput X Y r).X i)
    (binaryTensorPatternSubgroup r) (fun k => (binaryTensorOrbitInput X Y r k).X i)
    (fun k => (binaryTensorOrbitInputInclusion X Y r k).f i)
    (fun k => (binaryTensorOrbitInputProjection X Y r k).f i)
    (fun k => binaryTensorOrbitInput_diagonal X Y r k i)
    (fun k => binaryTensorOrbitInput_self X Y r k i)
    (fun k l hkl => binaryTensorOrbitInput_cross X Y r k l hkl i)

/-- 指定した双錐は、実際の入力表現の有限直和分解である。 -/
def binaryTensorOrbitBiconeIsBilimit (i : ℤ) :
    (binaryTensorOrbitBicone X Y r i).IsBilimit :=
  finiteInductionBiconeIsBilimit ((binaryTensorFullInput X Y r).X i)
    (binaryTensorPatternSubgroup r) (fun k => (binaryTensorOrbitInput X Y r k).X i)
    (fun k => (binaryTensorOrbitInputInclusion X Y r k).f i)
    (fun k => (binaryTensorOrbitInputProjection X Y r k).f i)
    (fun k => binaryTensorOrbitInput_diagonal X Y r k i)
    (fun k => binaryTensorOrbitInput_self X Y r k i)
    (fun k l hkl => binaryTensorOrbitInput_cross X Y r k l hkl i)
    (fun f g => binaryTensorOrbitInduced_hom_ext X Y r i f g)

end SerrePositivity.EInfinity
