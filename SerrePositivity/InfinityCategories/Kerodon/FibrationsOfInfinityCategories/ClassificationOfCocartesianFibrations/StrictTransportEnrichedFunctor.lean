module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：left fibrations から strict transport の像への豊穣関手と coherent nerve 上の比較。
方針：相対 Hom の作用を単位・合成と整合させ、Hom の同値を coherent nerve の充満忠実性へ移す。
規約：一般の coherent な空間値図式の strictification は別の証明課題。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な表現の写像空間を coherent な中間 ∞ 圏へ束ねる。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict transport の相対 Hom の作用を一対象で評価すると相対 Hom の豊穣後合成になる。
方針：対象成分の射の定義を計算する。
規約：射影の充填性は不要。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、豊穣関手の単位・合成を成分で検証する。 -/
lemma leftStrictTransportMappingSpaceMap_component
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom (Over.mk (nerveMap (Under.forget c))) (Over.mk p) (Over.mk q) := rfl

/-- 概要：strict transport は left fibrations の単体的圏から、その像の単体的圏への豊穣関手。
方針：相対 Hom への作用を各対象で後合成として計算し、後合成の単位則と合成則を使う。
規約：対象を同値類で商にしない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の高次の射への作用を coherent nerve に移す。 -/
def leftStrictTransportEnriched {C : Type u} [Category.{u} C] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportImageObject
  map p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap p.val.hom q.val.hom
  map_id p := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingHom_ext
    intro c
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity p.val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap p.val.hom p.val.hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p.val.hom) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p.val.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent _ _ c
    rw [Category.assoc, leftStrictTransportMappingSpaceMap_component,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_component]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom_id (Over.mk (nerveMap (Under.forget c))) p.val
  map_comp p q r := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingHom_ext
    intro c
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition p.val q.val r.val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap p.val.hom r.val.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p.val.hom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram r.val.hom) c =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap p.val.hom q.val.hom ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap q.val.hom r.val.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p.val.hom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q.val.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram r.val.hom)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent _ _ c
    rw [Category.assoc, leftStrictTransportMappingSpaceMap_component,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_component, ← Category.assoc,
      tensorHom_comp_tensorHom, leftStrictTransportMappingSpaceMap_component,
      leftStrictTransportMappingSpaceMap_component]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom_comp (Over.mk (nerveMap (Under.forget c))) p.val q.val r.val

/-- 概要：strict transport の豊穣関手を coherent nerve に写した比較関手。
方針：thickening からの各豊穣図式へ strict transport を後合成する。
規約：比較先は strict transport の像の coherent nerve。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、既存の相対 Hom の同値を ∞ 圏の関手にまとめる。 -/
noncomputable def leftStrictTransportInfinityMap (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramInfinity C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (leftStrictTransportEnriched (C := C))

/-- 概要：strict transport の像への coherent な比較は充満忠実。
方針：豊穣 Hom の実際の比較射の同値性を coherent nerve の充満忠実性の判定へ適用する。
規約：全写像空間の同値性を使い、ホモトピー圏の Hom の全単射には弱めない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な表現への ∞ 圏の比較の写像空間の検証。 -/
lemma leftStrictTransportInfinityMap_isFullyFaithful (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (leftStrictTransportInfinityMap C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff (leftStrictTransportEnriched (C := C))).mpr
  intro p q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportMappingSpaceMap_isQCatEquivalence p.val.hom q.val.hom

/-- 概要：coherent な strict transport 比較の対象での値は元の strict transport 図式。
方針：豊穣後合成の coherent nerve の頂点公式を使う。
規約：束縛した left fibration p の標準頂点を入力する。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、比較関手の本質的全射性と元の候補の対象の同定。 -/
lemma leftStrictTransportInfinityMap_vertex {C : Type u} [Category.{u} C]
    (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) :
    (leftStrictTransportInfinityMap C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportImageObject p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (leftStrictTransportEnriched (C := C)) p

/-- 概要：strict transport の像への coherent な比較は本質的全射。
方針：任意の coherent 頂点を像の図式へ戻し、その図式を表す fibration の存在を使う。
規約：標的は strict transport の像。全ての空間値 coherent 図式の表現可能性は主張しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な表現の中間 ∞ 圏との比較の対象での検証。 -/
lemma leftStrictTransportInfinityMap_isEssentiallySurjective (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (leftStrictTransportInfinityMap C) := by
  intro y
  let F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y
  obtain ⟨p, hp⟩ := F.property
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p, ?_⟩
  rw [leftStrictTransportInfinityMap_vertex]
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportImageObject p = F := Subtype.ext hp
  exact ⟨eqToIso (congrArg SSet.HomotopyCategory.mk
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y)))⟩

/-- 概要：left fibrations の ∞ 圏から strict transport の像の coherent nerve への比較は同値。
方針：豊穣 Hom の比較による充満忠実性と像への本質的全射性を同値判定へ適用する。
規約：一般の coherent な図式の関手 ∞ 圏との同値は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な表現の高次の写像空間を保持した比較。 -/
lemma leftStrictTransportInfinityMap_isQCatEquivalence (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (leftStrictTransportInfinityMap C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (leftStrictTransportInfinityMap_isFullyFaithful C)
    (leftStrictTransportInfinityMap_isEssentiallySurjective C)

/-- 概要：left fibrations の ∞ 圏と strict transport の像の coherent nerve の同値データ。
方針：実際の strict transport の coherent な比較の同値性から逆射と二つの関手同型を選ぶ。
規約：順方向は豊穣関手の coherent nerve に固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な空間値図式の比較へ進むための中間の同値。 -/
noncomputable def leftStrictTransportInfinityEquivalence (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramInfinity C) :=
  (leftStrictTransportInfinityMap_isQCatEquivalence C).choose

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
