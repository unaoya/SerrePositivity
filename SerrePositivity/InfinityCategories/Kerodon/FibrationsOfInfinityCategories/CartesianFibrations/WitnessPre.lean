module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianSquare

/-!
概要：pullback 正方形に沿う実際の表現空間の前合成。
方針：四角形の前合成を表現条件の全部分複体へ持ち上げる。
規約：恒等射則と合成則を厳密に保つ。
使われ方：底上の図式に沿う表現の降下。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：実際の表現空間の四角形空間への包含は単射。
方針：全部分複体の包含の単射性を回収する。
規約：非空性は不要。
使われ方：表現の降下の一意性を周囲の四角形で検査する。 -/
instance transportWitnessSpaceι_mono {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p) := inferInstanceAs
  (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p)).ι)

/-- 概要：pullback 正方形の前合成は表現の頂点条件を保つ。
方針：実際の表現を回収し前合成の fiber 条件を使う。
規約：頂点の非空性を仮定しない。
使われ方：表現空間の全部分複体への持ち上げ。 -/
lemma isTransportWitnessVertex_preSquare {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace q.hom) _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex q.hom v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p.hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre f).app _ v) := by
  obtain ⟨R, rfl⟩ := hv
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.isTransportWitnessVertex_iff_isRepresentation]
  exact R.toSquare.isRepresentation_preSquare R.toSquare_isRepresentation f hf

/-- 概要：pullback 正方形に沿う実際の表現空間の前合成。
方針：四角形の前合成を表現の全部分複体へ持ち上げる。
規約：底側と全空間側をともに保持する。
使われ方：余極限図式の各項への表現の制限。 -/
def transportWitnessPre {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace q.hom ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι q.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre f)
    (fun v ↦ isTransportWitnessVertex_preSquare f hf v.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v))

/-- 概要：pullback 正方形の表現の前合成は周囲の四角形の前合成を回収する。
方針：全部分複体への lift の包含公式。
規約：全高次単体の厳密な等式。
使われ方：表現の降下と四角形の降下の比較。 -/
lemma transportWitnessPre_ι {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) :
    transportWitnessPre f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι q.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：表現空間の前合成の恒等正方形は恒等射。
方針：包含後に周囲の四角形の恒等射則を使う。
規約：pullback 性の証明の選択に依存しない。
使われ方：表現空間の反変関手の恒等射則。 -/
lemma transportWitnessPre_id (p : Arrow SSet.{u + 1}) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom]
    (h : IsPullback (𝟙 p.left) p.hom p.hom (𝟙 p.right)) :
    transportWitnessPre (𝟙 p) h = 𝟙 _ := by
  let : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p.hom) := inferInstanceAs
    (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p.hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p.hom)).ι)
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p.hom)).1
  rw [transportWitnessPre_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_id, Category.comp_id, Category.id_comp]

/-- 概要：pullback 正方形の合成は表現空間の前合成を反変に合成する。
方針：包含後に周囲の四角形の合成則を使う。
規約：各 pullback 性の証明の選択に依存しない。
使われ方：表現空間の反変関手の合成則。 -/
lemma transportWitnessPre_comp {p q r : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r.hom]
    (f : p ⟶ q) (g : q ⟶ r)
    (hf : IsPullback f.left p.hom q.hom f.right)
    (hg : IsPullback g.left q.hom r.hom g.right)
    (hfg : IsPullback (f ≫ g).left p.hom r.hom (f ≫ g).right) :
    transportWitnessPre (f ≫ g) hfg = transportWitnessPre g hg ≫ transportWitnessPre f hf := by
  let : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p.hom) := inferInstanceAs
    (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p.hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p.hom)).ι)
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p.hom)).1
  rw [transportWitnessPre_ι, Category.assoc, transportWitnessPre_ι, ← Category.assoc,
    transportWitnessPre_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
