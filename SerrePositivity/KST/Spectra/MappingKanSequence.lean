module

public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomTensorStrength

/-!
概要：Kan 列へ点つき内部 Hom を各段で施す構成。
方針：smash と内部 Hom の交換射の後に元の構造射を施す。
規約：新しい列の単射性や Ω 条件は主張しない。
使われ方：BF 1978 §2、HTT A.3.3。自由な path の Kan 列と厳密な端点評価。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace KanSequence

/-- 概要：点つき対象 A からの内部 Hom を Kan 列の各段に取る。
方針：テンソル交換射と元の構造射の後合成を使う。
規約：A の Kan 性は不要。
使われ方：BF 1978 §2、HTT A.3.3。path 列の実構成。 -/
def mapping (A : PointedSimplicialSet.{u}) (X : KanSequence.{u}) : KanSequence.{u} where
  level n := {
    space := PointedObject.basedHom A (X.level n).space
    kan := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _ }
  sigma n := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A (X.level n).space ≫
    (ihom A).map (X.sigma n)

/-- 概要：内部 Hom の源の制限は Kan 列の厳密な射を与える。
方針：テンソル交換と源の制限の自然性を構造射へ合成する。
規約：源の射には単射性を仮定しない。
使われ方：BF 1978 §2、HTT A.3.3。path 列の端点の射。 -/
def mappingPre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) (X : KanSequence.{u}) :
    Hom (mapping B X) (mapping A X) where
  app n := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space
  comm n := by
    change PointedSimplicialSet.circle.{u} ◁ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A (X.level n).space ≫
        (ihom A).map (X.sigma n)) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} B (X.level n).space ≫
        (ihom B).map (X.sigma n)) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level (n + 1)).space
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.natural_pre_assoc, MonoidalClosed.pre_comm_ihom_map]

/-- 概要：内部 Hom の標的の射は Kan 列の厳密な射を与える。
方針：テンソル交換の自然性と元の構造射の可換式を使う。
規約：点つき内部 Hom の各段の後合成。
使われ方：BF 1978 §2、HTT A.3.3。path 列の関手性。 -/
def mappingPost (A : PointedSimplicialSet.{u}) {X Y : KanSequence.{u}} (f : Hom X Y) :
    Hom (mapping A X) (mapping A Y) where
  app n := PointedObject.basedHomMap A (f.app n)
  comm n := by
    change PointedSimplicialSet.circle.{u} ◁ (ihom A).map (f.app n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A (Y.level n).space ≫
        (ihom A).map (Y.sigma n)) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A (X.level n).space ≫
        (ihom A).map (X.sigma n)) ≫ (ihom A).map (f.app (n + 1))
    rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.natural_post_assoc, Category.assoc, ← Functor.map_comp,
      f.comm n, Functor.map_comp]

/-- 概要：単位からの内部 Hom の列を元の列へ評価する厳密な射。
方針：単位の自然同型とテンソル交換の単位での計算を使う。
規約：各段の射は unitIsoSelf の順方向。
使われ方：BF 1978 §2、HTT A.3.3。端点評価を元の列へ戻す。 -/
def mappingUnitEvaluation (X : KanSequence.{u}) :
    Hom (mapping (𝟙_ PointedSimplicialSet.{u}) X) X where
  app n := (MonoidalClosed.unitIsoSelf (X := (X.level n).space)).hom
  comm n := by
    have h : (ihom (𝟙_ PointedSimplicialSet.{u})).map (X.sigma n) ≫
        (MonoidalClosed.unitIsoSelf (X := (X.level (n + 1)).space)).hom =
      (MonoidalClosed.unitIsoSelf (X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).hom ≫ X.sigma n :=
        (MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality (X.sigma n)
    change _ = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u}
      (𝟙_ PointedSimplicialSet.{u}) _ ≫
      (ihom (𝟙_ PointedSimplicialSet.{u})).map (X.sigma n)) ≫ _
    rw [Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map_unit]

/-- 概要：元の Kan 列から単位を源とする内部 Hom の列への逆射。
方針：各段の単位同型の逆を取り、順方向の構造可換式を打ち消す。
規約：構造射との可換性も厳密。
使われ方：BF 1978 §2、HTT A.3.3。定数 path の列の射。 -/
def mappingUnitInverse (X : KanSequence.{u}) : Hom X (mapping (𝟙_ PointedSimplicialSet.{u}) X) where
  app n := (MonoidalClosed.unitIsoSelf (X := (X.level n).space)).inv
  comm n := by
    let e n := MonoidalClosed.unitIsoSelf (X := (X.level n).space)
    apply (cancel_mono (e (n + 1)).hom).mp
    have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u}
        (𝟙_ PointedSimplicialSet.{u}) (X.level n).space ≫
        (ihom (𝟙_ PointedSimplicialSet.{u})).map (X.sigma n) ≫ (e (n + 1)).hom =
        PointedSimplicialSet.circle.{u} ◁ (e n).hom ≫ X.sigma n :=
      (mappingUnitEvaluation X).comm n |>.symm
    change (PointedSimplicialSet.circle.{u} ◁ (e n).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u}
        (𝟙_ PointedSimplicialSet.{u}) (X.level n).space ≫
        (ihom (𝟙_ PointedSimplicialSet.{u})).map (X.sigma n))) ≫ (e (n + 1)).hom =
        (X.sigma n ≫ (e (n + 1)).inv) ≫ (e (n + 1)).hom
    rw [Category.assoc, Category.assoc, h, ← whiskerLeft_comp_assoc]
    simp only [Iso.inv_hom_id, whiskerLeft_id, Category.id_comp,
      Category.assoc, Category.comp_id]

/-- 概要：Kan 列の自由な path 列。
方針：自由区間からの内部 Hom を各段に取る。
規約：各段は Kan だが構造射の単射性をまだ要求しない。
使われ方：BF 1978 §2、Goerss–Jardine I §7。mapping path 置換。 -/
abbrev freePath (X : KanSequence.{u}) : KanSequence.{u} := mapping _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} X

/-- 概要：自由な path 列から元の列への厳密な端点評価。
方針：端点による制限と単位からの内部 Hom の評価を合成する。
規約：面添字一が始点、零が終点。
使われ方：BF 1978 §2、Goerss–Jardine I §7。mapping path の二つの射影。 -/
def freePathEvaluation (X : KanSequence.{u}) (i : Fin 2) : Hom X.freePath X :=
  (mappingPre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i) X).comp (mappingUnitEvaluation X)

/-- 概要：元の列から自由な path 列への定数 path の厳密な射。
方針：単位の内部 Hom の逆と自由区間を潰す射の制限を合成する。
規約：各段は既存の定数 path の射。
使われ方：BF 1978 §2、Goerss–Jardine I §7。mapping path の比較射。 -/
def freePathConstant (X : KanSequence.{u}) : Hom X X.freePath :=
  (mappingUnitInverse X).comp (mappingPre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse.{u} X)

/-- 概要：列の定数 path の両端点評価は厳密に恒等射。
方針：各段の定数 path の計算式を使う。
規約：各段の射の等式。
使われ方：BF 1978 §2。mapping path の厳密な因子分解。 -/
@[reassoc (attr := simp)]
theorem freePathConstant_evaluation (X : KanSequence.{u}) (i : Fin 2) (n : ℕ) :
    X.freePathConstant.app n ≫ (X.freePathEvaluation i).app n = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath_endpoint (X.level n).space i

end KanSequence

end

end SerrePositivity.KST.Spectra
