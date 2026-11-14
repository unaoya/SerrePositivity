module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorExt
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatJoinRightTensor
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.LaxCoslice
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.LaxCosliceUncurry

/-! # 太い coslice の普遍性

概要：太い coslice への族と左図式を固定する太い余錐は同値である。
方針：curry と uncurry の両逆則を円柱と両因子で計算する。
規約：任意の単体集合をパラメーターに取る。使われ方：余錐の模型の比較同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：curry の普遍族の右端での評価は元の右因子の値。
方針：右直積比較と fat join の右包含の計算を使う。
規約：左図式の固定条件は不要。使われ方：普遍性の一方の逆則。 -/
lemma laxCosliceRightInput_curryFamily {A K X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceRightInput A K ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A ≫ F := by
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceRightInput A K =
      lift (stdSimplex.isTerminalObj₀.from A) (𝟙 A) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0] ▷ A) := rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily, hs]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0] ▷ A), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableFatJoinTensorRight_inr]
  simp only [reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map]
  rfl

/-- 概要：curry の普遍族の円柱での評価は元の円柱の値。
方針：右直積比較の円柱上の式と成分の並べ替えを使う。
規約：左図式の固定条件は不要。使われ方：普遍性の一方の逆則。 -/
lemma laxCosliceCylinderInput_curryFamily {A K X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCylinderInput A K ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K A ≫ F := by
  let C := (K ⊗ (Δ[1] : SSet.{u})) ⊗ A
  let c : C ⟶ (((K ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[0]) ⊗ A) :=
    lift (lift (fst (K ⊗ Δ[1]) A) (stdSimplex.isTerminalObj₀.from C))
      (snd (K ⊗ Δ[1]) A)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCylinderInput A K = c ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K Δ[0] ▷ A) := rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily, hs]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K Δ[0] ▷ A), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableFatJoinTensorRight_cylinder]
  simp only [Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map]
  rfl

/-- 概要：太い余錐の関手を curry してから uncurry すると元に戻る。
方針：円柱と両因子で評価を比較する。
規約：左図式の固定条件を仮定する。使われ方：太い coslice の普遍性。 -/
lemma laxCosliceUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry F hF) = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_cylinder]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCylinderInput A K ≫ uncurry (curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily F)) = _
    rw [uncurry_curry, laxCosliceCylinderInput_curryFamily]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_fixed, hF]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_inr]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceRightInput A K ≫ uncurry (curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily F)) = _
    rw [uncurry_curry, laxCosliceRightInput_curryFamily]

/-- 概要：太い coslice の族を uncurry した族は元の普遍族に戻る。
方針：円柱と右因子で零単体の一意性を使い、左因子で固定条件を使う。
規約：quasicategory 性は不要。使われ方：普遍性のもう一方の逆則。 -/
lemma laxCosliceCurryFamily_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry f) =
      uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_tensorRight_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K (Δ[0] : SSet.{u}) ▷ A),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableFatJoinTensorRight_cylinder]
    simp only [Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map]
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_cylinder]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟨k, t⟩, z⟩, a⟩
    have hz : (stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a = z := by
      apply stdSimplex.ext
      intro i
      omega
    change (uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))).app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K Δ[0]).app (Opposite.op ⦋n⦌)
        ((k, t), (stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a), a) = _
    rw [hz]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily_fixed _ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_fixed f), _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceFamily_fixed]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K (Δ[0] : SSet.{u}) ▷ A), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableFatJoinTensorRight_inr]
    simp only [reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map]
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_inr]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨z, a⟩
    have hz : (stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a = z := by
      apply stdSimplex.ext
      intro i
      omega
    change (uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))).app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0]).app (Opposite.op ⦋n⦌)
        ((stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a), a) = _
    rw [hz]
    rfl

/-- 概要：太い coslice の族を uncurry して curry すると元に戻る。
方針：fiber の包含後に uncurry して普遍族を比較する。
規約：任意のパラメーター。使われ方：太い coslice の普遍性の逆則。 -/
lemma laxCosliceCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry f) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_fixed f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (Δ[0] : SSet.{u}))).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
  change curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry f)) = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
  apply uncurry_injective
  rw [uncurry_curry, laxCosliceCurryFamily_uncurry]

/-- 概要：太い coslice への族と左図式を固定する太い余錐の射は同値。
方針：curry と uncurry の両逆則を使う。
規約：パラメーター・図式・値域の quasicategory 性は不要。
使われ方：coslice と余錐の関手圏の比較。 -/
def laxCosliceHomEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) ≃ {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ F = p} where
  toFun f := ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry f, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_fixed f⟩
  invFun F := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry F.val F.property
  left_inv := laxCosliceCurry_uncurry
  right_inv F := Subtype.ext (laxCosliceUncurry_curry F.val F.property)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
