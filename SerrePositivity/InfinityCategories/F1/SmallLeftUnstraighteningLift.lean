module

public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningOverMap

/-!
概要：小さい全空間から unstraightening への比較射を元の宇宙へ降ろす。
方針：標的の縮小同型を使って射を降ろし、fiber の可換式で同値性を反映する。
規約：元の全空間 E と底 B は宇宙 u に置く。
使われ方：Kerodon Corollary 5.6.0.6、straightening 後の小さい復元比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：持ち上げた小さい全空間からの射を小さい unstraightening へ降ろす。
方針：標的の縮小同型の逆射を合成して ULift を降ろす。
規約：底上の条件は定義に要求しない。
使われ方：Kerodon Corollary 5.6.0.6、復元比較の小さい順方向。 -/
noncomputable def smallLeftUnstraighteningLift {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F) :
    E ⟶ smallLeftUnstraightening F :=
  uliftMorphismDown (f ≫ (smallLeftUnstraighteningIso F).inv)

/-- 概要：降ろした比較射の持ち上げは元の比較射を回収する。
方針：ULift の往復と縮小同型の往復を消す。
規約：元の射 f 自体との厳密な可換式。
使われ方：Kerodon Corollary 5.6.0.6、底と fiber の可換性の移送。 -/
lemma smallLeftUnstraighteningLift_naturality {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningLift F f) ≫
      (smallLeftUnstraighteningIso F).hom = f := by
  rw [smallLeftUnstraighteningLift, uliftMorphismDown_lift, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 概要：元の比較が底を保つなら小さい比較も底を厳密に保つ。
方針：宇宙持ち上げの忠実性と全空間の比較の可換式を使う。
規約：射影の等式を元の宇宙で述べる。
使われ方：Kerodon Remark 5.6.2.5、小さい復元の底上の条件。 -/
lemma smallLeftUnstraighteningLift_projection {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (p : E ⟶ B)
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F)
    (h : f ≫ leftUnstraighteningProjection F = (SSet.uliftFunctor.{u + 1, u}).map p) :
    smallLeftUnstraighteningLift F f ≫ smallLeftUnstraighteningProjection F = p := by
  apply (SSet.uliftFunctor.{u + 1, u}).map_injective
  rw [Functor.map_comp, ← smallLeftUnstraighteningIso_projection F,
    ← Category.assoc, smallLeftUnstraighteningLift_naturality, h]

/-- 概要：小さい比較射の fiber 射は元の比較射の fiber 射と可換。
方針：元の全空間への包含後に全空間の可換式を計算する。
規約：始域では ULift と fiber の交換、終域では縮小の fiber 同型を使う。
使われ方：Kerodon Corollary 5.6.0.6、元の比較の同値性を小さい fiber へ移す。 -/
lemma smallLeftUnstraighteningLift_fiber_naturality {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (p : E ⟶ B)
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F)
    (h : f ≫ leftUnstraighteningProjection F = (SSet.uliftFunctor.{u + 1, u}).map p)
    (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap p
      (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningLift F f)
        (smallLeftUnstraighteningLift_projection F p f h) b) ≫
      (smallLeftUnstraighteningFiberIso F b).hom =
    (uliftVertexFiberIso p b).hom ≫ vertexFiberMap
      ((SSet.uliftFunctor.{u + 1, u}).map p) (leftUnstraighteningProjection F)
        f h (ULift.up b) := by
  apply vertexFiber_hom_ext (leftUnstraighteningProjection F) (ULift.up b)
  simp only [Category.assoc, vertexFiberMap_ι]
  rw [smallLeftUnstraighteningFiberIso_hom_ι, ← Category.assoc,
    ← Functor.map_comp, vertexFiberMap_ι, Functor.map_comp, Category.assoc,
    smallLeftUnstraighteningLift_naturality, ← Category.assoc, uliftVertexFiberIso_hom_ι]

/-- 概要：底上の前合成同値を小さい unstraightening への前合成同値へ降ろせる。
方針：各 Kan fiber の同値を宇宙持ち上げから反映し、全空間の同値へ戻す。
規約：p は left fibration、底 B は quasicategory。
使われ方：Kerodon Corollary 5.6.0.6、小さい復元比較の同値性。 -/
lemma smallLeftUnstraighteningLift_isPrecompositionEquivalence
    {E B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (p : E ⟶ B) [LeftFibration p]
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F)
    (h : f ≫ leftUnstraighteningProjection F = (SSet.uliftFunctor.{u + 1, u}).map p)
    (ef : IsPrecompositionEquivalence f) :
    IsPrecompositionEquivalence (smallLeftUnstraighteningLift F f) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers p
    (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningLift F f)
      (smallLeftUnstraighteningLift_projection F p f h)
  intro b
  apply (isQCatEquivalence_ulift_iff_of_kan _).mp
  apply (qCatEquivalenceOfIso (smallLeftUnstraighteningFiberIso F b)).isQCatEquivalence.cancel_right
  change IsQCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap p
    (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningLift F f)
      (smallLeftUnstraighteningLift_projection F p f h) b) ≫
        (smallLeftUnstraighteningFiberIso F b).hom)
  rw [smallLeftUnstraighteningLift_fiber_naturality F p f h b]
  exact (qCatEquivalenceOfIso (uliftVertexFiberIso p b)).isQCatEquivalence.comp
    (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).map p) (leftUnstraighteningProjection F) f h ef (ULift.up b))

end SerrePositivity.InfinityCategories
