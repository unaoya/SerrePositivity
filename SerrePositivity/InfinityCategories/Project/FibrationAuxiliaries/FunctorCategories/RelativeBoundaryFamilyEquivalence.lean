module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeBoundaryFamilyFiber

/-!
概要：動く底と境界を持つ全 lift の前合成比較の fiber ごとの同値性。
方針：各パラメーターのデータを関手で表し、厳密な fiber 同型で固定境界の比較へ移す。
規約：パラメーターの各頂点だけでなく fiber 空間全体の同値を示す。
使われ方：分類図式の族全体の円柱比較の同値判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：前合成同値による動く境界固定 lift の比較は各パラメーター fiber で同値。
方針：二つの厳密な fiber 同型が固定境界比較と可換することを確認する。
規約：i の単射性は要求せず j と j≫i の単射性だけを使う。
使われ方：分類図式を動かしたまま比較を同値にする主要入力。 -/
lemma relativeBoundaryFamilyPre_fiber_isQCatEquivalence
    {A D C E B L : SSet.{u}} [Quasicategory B]
    (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (j : C ⟶ D)
    [Mono j] [Mono (j ≫ i)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p)
    (d : L ⟶ rA.pt) (l : L _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rA d)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rD (d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre i j p rA rD d)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre_projection i j p rA rD d) l) := by
  obtain ⟨a, v, hv, hz₀, hz₁⟩ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.exists_relativeHomBoundaryVertex (j ≫ i) p rA (d.app _ l)
  have hvD : v ≫ p = j ≫ (i ≫ a) := by simpa only [Category.assoc] using hv
  have hD₀ : rD.fst.app _ ((d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD).app _ l) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v := by
    have h := congrArg (fun w ↦ w.app (Opposite.op ⦋0⦌) (d.app _ l))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre_fst i j p rA rD)
    exact h.trans hz₀
  have hD₁ : rD.snd.app _ ((d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD).app _ l) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a) := by
    have h := congrArg (fun w ↦ w.app (Opposite.op ⦋0⦌) (d.app _ l))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre_snd i j p rA rD)
    change rD.snd.app _ ((d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD).app _ l) =
      ((pre i).app B).app _ (rA.snd.app _ (d.app _ l)) at h
    rw [hz₁] at h
    exact h
  let eA := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyStrictFiberIso (j ≫ i) p rA d l a v hv hz₀ hz₁
  let eD := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyStrictFiberIso j p rD
    (d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD) l (i ≫ a) v hvD hD₀ hD₁
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a (j ≫ i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (i ≫ a) j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_comp p a i j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p ((j ≫ i) ≫ a) v hv)
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rA d)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rD (d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD))
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre i j p rA rD d)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre_projection i j p rA rD d) l
  have heA := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyStrictFiberIso_hom_ι (j ≫ i) p rA d l a v hv hz₀ hz₁
  have heD := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyStrictFiberIso_hom_ι j p rD
    (d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD) l (i ≫ a) v hvD hD₀ hD₁
  have hkι : k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (i ≫ a) j)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (j ≫ (i ≫ a)) v hvD) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a (j ≫ i))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p ((j ≫ i) ≫ a) v hv) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ _
  have hcomm : F ≫ eD.hom = eA.hom ≫ k := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (i ≫ a) j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (j ≫ (i ≫ a)) v hvD)
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
    simp only [Category.assoc]
    rw [heD, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre_curry]
    change _ = eA.hom ≫ k ≫ _ ≫ _
    rw [← Category.assoc k, hkι]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι p a i]
    simpa only [Category.assoc] using congrArg (fun w ↦ w ≫ (pre i).app E) heA.symm
  have hk : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence k := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBoundaryMap_isQCatEquivalence p a i hi j _
  have hcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (F ≫ eD.hom) := by
    rw [hcomm]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso eA).isQCatEquivalence.comp hk
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso eD).isQCatEquivalence.cancel_right hcomp

/-- 概要：quasicategory のパラメーター空間上で動く底と境界の比較は空間全体で同値。
方針：パラメーター射影の left fibration 性と全 fiber の比較を合わせる。
規約：固定図式の同値だけでなく実際の族全体の射について結論する。
使われ方：両端固定の区間写像空間上の輸送円柱比較。 -/
lemma relativeBoundaryFamilyPre_isQCatEquivalence
    {A D C E B L : SSet.{u}} [Quasicategory B] [Quasicategory L]
    (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (j : C ⟶ D)
    [Mono j] [Mono (j ≫ i)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p)
    (d : L ⟶ rA.pt) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre i j p rA rD d) := by
  let : Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace rA d) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rA d)
  let : Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace rD
      (d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD)) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rD _)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rA d)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rD (d ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre i j p rA rD))
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre i j p rA rD d)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyPre_projection i j p rA rD d)
  exact relativeBoundaryFamilyPre_fiber_isQCatEquivalence i hi j p rA rD d

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
