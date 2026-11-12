module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeBoundaryFamilySpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberPullback

/-!
概要：相対内部 Hom の fiber を底と境界を固定した相対関手空間に同定する。
方針：二射影の固定条件を二段の頂点 fiber に並べ直す。
規約：全ての高次 lift を厳密に保つ。
使われ方：動く分類図式の族の fiber に固定図式の比較を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：相対内部 Hom の fiber は固定底の相対関手の境界 fiber と厳密に同型。
方針：底の固定条件と境界の固定条件を順に vertexFiberLift に入れる。
規約：z の二成分を実際の関手 a,v で指定する。
使われ方：族の fiber の同値性を既証明の境界固定比較で判定する。 -/
def relativeHomBoundaryFiberIso {A C E B : SSet.{u}} (i : C ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (a : A ⟶ B) (v : C ⟶ E)
    (hv : v ≫ p = i ≫ a) (z : r.pt _⦋0⦌)
    (hz₀ : r.fst.app _ z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v) (hz₁ : r.snd.app _ z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r.π z ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ a) v hv) := by
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ a) v hv
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r.π z
  let Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b
  let xι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r.π z
  let yι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b
  let y₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  have hxbase : xι ≫ (ihom A).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
    calc
      _ = (xι ≫ r.π) ≫ r.snd := by rw [Category.assoc, r.π_snd]; rfl
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp, hz₁]
  have hxboundary : xι ≫ (pre i).app E = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v) := by
    calc
      _ = (xι ≫ r.π) ≫ r.fst := by rw [Category.assoc, r.π_fst]; rfl
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp, hz₀]
  let F₀ : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ xι hxbase
  have hF₀ : F₀ ≫ y₀ = xι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hFboundary : F₀ ≫ q = SSet.const b := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom C).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
    change F₀ ≫ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom C).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι, ← Category.assoc]
    change (F₀ ≫ y₀) ≫ (pre i).app E = _
    rw [hF₀, hxboundary, SSet.const_comp]
    rfl
  let F : X ⟶ Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q b F₀ hFboundary
  have hF : F ≫ yι = F₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hy : (yι ≫ y₀) ≫ r.π = SSet.const z := by
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst]
      change (yι ≫ y₀) ≫ (pre i).app E = _
      rw [Category.assoc]
      change yι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app E) = _
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp,
        SSet.const_comp, hz₀]
      rfl
    · rw [Category.assoc, r.π_snd]
      change (yι ≫ y₀) ≫ (ihom A).map p = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.const_comp, hz₁]
  let G : Y ⟶ X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift r.π z (yι ≫ y₀) hy
  have hG : G ≫ xι = yι ≫ y₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  refine { hom := F, inv := G, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext r.π z
    change (F ≫ G) ≫ xι = (𝟙 X) ≫ xι
    rw [Category.assoc, hG, ← Category.assoc, hF, hF₀, Category.id_comp]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
    change ((G ≫ F) ≫ yι) ≫ y₀ = ((𝟙 Y) ≫ yι) ≫ y₀
    rw [Category.assoc G F yι, hF, Category.assoc, hF₀, hG, Category.id_comp]

/-- 概要：相対内部 Hom の fiber の同型は元の全空間の関手を保持する。
方針：二段の fiber への持ち上げの包含を計算する。
規約：射そのものの厳密な等式。
使われ方：fiber 比較と前合成の可換性。 -/
lemma relativeHomBoundaryFiberIso_hom_ι {A C E B : SSet.{u}} (i : C ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (a : A ⟶ B) (v : C ⟶ E)
    (hv : v ≫ p = i ≫ a) (z : r.pt _⦋0⦌)
    (hz₀ : r.fst.app _ z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v) (hz₁ : r.snd.app _ z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) :
    (relativeHomBoundaryFiberIso i p r a v hv z hz₀ hz₁).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ a) v hv) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r.π z := rfl

/-- 概要：相対内部 Hom の頂点の二成分を実際の可換な底と境界写像で回収する。
方針：内部 Hom の頂点対応と引き戻し条件を使う。
規約：射影の充填性は要求しない。
使われ方：族の各 fiber へ固定図式の比較を適用する入力。 -/
lemma exists_relativeHomBoundaryVertex {A C E B : SSet.{u}} (i : C ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (z : r.pt _⦋0⦌) :
    ∃ (a : A ⟶ B) (v : C ⟶ E) (_hv : v ≫ p = i ≫ a),
      r.fst.app _ z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v ∧ r.snd.app _ z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a := by
  obtain ⟨a, ha⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B).surjective (r.snd.app _ z)
  obtain ⟨v, hv⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C E).surjective (r.fst.app _ z)
  have hc : v ≫ p = i ≫ a := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    have h := congrArg (fun w ↦ w.app (Opposite.op ⦋0⦌) z) r.isPullback.w
    change ((ihom C).map p).app _ (r.fst.app _ z) =
      ((pre i).app B).app _ (r.snd.app _ z) at h
    rw [← hv, ← ha] at h
    exact h
  exact ⟨a, v, hc, hv.symm, ha.symm⟩

/-- 概要：動く境界データのパラメーター fiber は相対内部 Hom の対応する fiber と同型。
方針：引き戻しの頂点 fiber の標準同型を使う。
規約：データもパラメーターも任意。
使われ方：固定底の境界 fiber への同定の第一段階。 -/
def relativeBoundaryFamilyFiberIso {A C E B L : SSet.{u}} {i : C ⟶ A} {p : E ⟶ B}
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) (l : L _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection r d) l ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r.π (d.app _ l) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r.π d l

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
