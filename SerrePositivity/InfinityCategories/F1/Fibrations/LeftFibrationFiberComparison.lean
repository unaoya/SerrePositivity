module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationNerveComparison
public import SerrePositivity.InfinityCategories.F1.Fibrations.FiberComparisonBaseChange
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.PrecompositionSimplexLocality
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderSourceIso

/-!
概要：任意の底上の left fibrations の射を fiber ごとに比較する判定。
方針：底の各標準単体を有限鎖の nerve へ移し、底変換した比較に scaffold の定理を使う。
規約：底の quasicategory 性は前合成同値の結論には不要。
使われ方：Kerodon Corollary 5.6.0.6、coherent 図式の復元候補を全空間で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：底を保つ比較射の各 fiber の同値性は、nerve を定義域とする底変換でも全空間の同値を与える。
方針：引き戻しの fiber 同型で元の fiber の同値へ戻し、通常の nerve 上の判定を適用する。
規約：底の圏の対象ごとの fiber の比較を使う。
使われ方：Kerodon Corollary 5.6.0.6、各標準単体上での比較。 -/
lemma isPrecompositionEquivalence_leftFibration_nerveBaseChange
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [LeftFibration p] [LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b))
    {C : Type u} [Category.{u} C] (g : nerve C ⟶ B) :
    IsPrecompositionEquivalence (fiberComparisonBaseChange p q f hf g) := by
  have : LeftFibration (pullback.snd p g) :=
    ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩
  have : LeftFibration (pullback.snd q g) :=
    ⟨leftFibrations.pullback_snd q g (LeftFibration.mem (p := q))⟩
  apply isPrecompositionEquivalence_of_leftFibration_nerve_fibers
    (pullback.snd p g) (pullback.snd q g) (fiberComparisonBaseChange p q f hf g)
    (fiberComparisonBaseChange_projection p q f hf g)
  intro c
  apply (qCatEquivalenceOfIso
    (vertexFiberPullbackIso q g (nerveVertex c))).isQCatEquivalence.cancel_right
  change IsQCatEquivalence
    (vertexFiberMap (pullback.snd p g) (pullback.snd q g)
      (fiberComparisonBaseChange p q f hf g)
      (fiberComparisonBaseChange_projection p q f hf g) (nerveVertex c) ≫
        (vertexFiberPullbackIso q g (nerveVertex c)).hom)
  rw [fiberComparisonBaseChange_fiber]
  exact (qCatEquivalenceOfIso (vertexFiberPullbackIso p g (nerveVertex c))).isQCatEquivalence.comp
    (h _)

/-- 概要：任意の底上の left fibrations の射は各 fiber で同値なら前合成同値。
方針：各標準単体を有限鎖の nerve と同定し、底変換の比較と全空間の局所性を使う。
規約：元の底 B は quasicategory でなくてもよい。
使われ方：Kerodon Corollary 5.6.0.6、unstraightening の全空間での比較。 -/
lemma isPrecompositionEquivalence_of_leftFibration_fibers
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [LeftFibration p] [LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsPrecompositionEquivalence f := by
  let u : Over.mk p ⟶ Over.mk q := Over.homMk f hf
  apply isPrecompositionEquivalence_of_pullback_stdSimplex u
  intro n s
  let g : nerve (ULift.{u} (Fin (n + 1))) ⟶ B := (stdSimplex.isoNerve n).inv ≫ s
  have hb := isPrecompositionEquivalence_leftFibration_nerveBaseChange p q f hf h g
  have hc := (isPrecompositionEquivalence_of_iso (pullbackSymmetry g p)).comp hb
  rw [fiberComparisonBaseChange_overPullbackMap] at hc
  have hd := (isPrecompositionEquivalence_of_iso (pullbackSymmetry g q)).cancel_right hc
  let e : Over.mk s ≅ Over.mk g := Over.isoMk (stdSimplex.isoNerve n) (by
    change (stdSimplex.isoNerve n).hom ≫ g = s
    exact Iso.hom_inv_id_assoc _ _)
  exact isPrecompositionEquivalence_over_natComponent_of_iso (overPullbackMapNat u) e hd

/-- 概要：left fibrations の底上の射は各 fiber で同値なら全空間の quasicategory の同値。
方針：fiber ごとの前合成同値の判定を適用し、quasicategory 間の同値を回収する。
規約：全空間の quasicategory 性は、底が quasicategory の場合は射影から従う。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元比較射の同値判定。 -/
lemma isQCatEquivalence_of_leftFibration_fibers
    {E E' B : SSet.{u}} [Quasicategory E] [Quasicategory E']
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsQCatEquivalence f :=
  (isPrecompositionEquivalence_of_leftFibration_fibers p q f hf h).isQCatEquivalence

end SerrePositivity.InfinityCategories
