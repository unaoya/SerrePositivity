module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTransform
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.LaxCoslice

/-! # 太い coslice の uncurry

概要：太い coslice の族から左図式を固定する太い余錐を取り出す。
方針：普遍族を円柱と右因子で評価し、二段の pushout で左図式と貼る。
規約：区間の向きと左図式を保つ。使われ方：余錐の族の比較の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：太い余錐の右端とパラメーターからなる入力。
方針：零単体への唯一の射を右端へ含める。
規約：パラメーターを第二因子に保つ。使われ方：uncurry の右成分。 -/
def laxCosliceRightInput (A K : SSet.{u}) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K (Δ[0] : SSet.{u}) ⊗ A :=
  lift (stdSimplex.isTerminalObj₀.from A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0]) (𝟙 A)

/-- 概要：太い余錐の円柱を太い零単体の余錐とパラメーターに分ける。
方針：左成分と区間を保ち、右成分をパラメーターへ送る。
規約：零単体は唯一の射で指定する。使われ方：uncurry の円柱成分。 -/
def laxCosliceCylinderInput (A K : SSet.{u}) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K (Δ[0] : SSet.{u}) ⊗ A :=
  lift (lift (fst (K ⊗ Δ[1]) A) (stdSimplex.isTerminalObj₀.from _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K Δ[0])
    (snd (K ⊗ Δ[1]) A)

/-- 概要：円柱の零端の入力は左包含とパラメーターに一致する。
方針：太い円柱の零端の潰しを計算する。
規約：左成分は図式の変数として残す。使われ方：固定図式との貼り合わせ。 -/
lemma laxCosliceCylinderInput_zero (A K : SSet.{u}) :
    (SSet.ι₀ (X := K) ▷ A) ≫ laxCosliceCylinderInput A K =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (Δ[0] : SSet.{u}) ▷ A) := by
  have ht : (SSet.ι₀ (X := K) ▷ A) ≫
      lift (fst (K ⊗ Δ[1]) A) (stdSimplex.isTerminalObj₀.from _) =
      lift (fst K A ≫ SSet.ι₀) (stdSimplex.isTerminalObj₀.from _) := by
    apply CartesianMonoidalCategory.hom_ext
    · rfl
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [laxCosliceCylinderInput, comp_lift, ← Category.assoc, ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_zero]
  rfl

/-- 概要：円柱の一端の入力は右成分の入力に射影する。
方針：太い円柱の一端の潰しと零単体の一意性を使う。
規約：左成分を忘れる。使われ方：右成分との貼り合わせ。 -/
lemma laxCosliceCylinderInput_one (A K : SSet.{u}) :
    (SSet.ι₁ (X := K) ▷ A) ≫ laxCosliceCylinderInput A K = snd K A ≫ laxCosliceRightInput A K := by
  have ht : (SSet.ι₁ (X := K) ▷ A) ≫
      lift (fst (K ⊗ Δ[1]) A) (stdSimplex.isTerminalObj₀.from _) =
      lift (fst K A ≫ SSet.ι₁) (stdSimplex.isTerminalObj₀.from _) := by
    apply CartesianMonoidalCategory.hom_ext
    · rfl
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [laxCosliceCylinderInput, comp_lift, ← Category.assoc, ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_one]
  apply CartesianMonoidalCategory.hom_ext
  · change stdSimplex.isTerminalObj₀.from (K ⊗ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0] =
      snd K A ≫ stdSimplex.isTerminalObj₀.from A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0]
    rw [← Category.assoc]
    congr 1
  · rfl

/-- 概要：太い coslice の族は左因子上で固定図式に定値。
方針：fiber の包含の射影を uncurry する。
規約：パラメーターの quasicategory 性は不要。使われ方：左成分の貼り合わせ。 -/
lemma laxCosliceFamily_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (Δ[0] : SSet.{u}) ▷ A) ≫
      uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) = fst K A ≫ p := by
  rw [← uncurry_pre_app, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨k, a⟩
  dsimp [uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex]
  rfl

/-- 概要：太い coslice の族を左図式を固定する fat join 上の射へ uncurry する。
方針：固定した左図式と普遍族の右端・円柱を貼り合わせる。
規約：左成分は p。使われ方：太い coslice の普遍性。 -/
def laxCosliceUncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc p (laxCosliceRightInput A K ≫ uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)))
    (laxCosliceCylinderInput A K ≫ uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)))
    (by rw [← Category.assoc, laxCosliceCylinderInput_zero, laxCosliceFamily_fixed])
    (by rw [← Category.assoc, laxCosliceCylinderInput_one, Category.assoc])

/-- 概要：太い coslice の uncurry は左図式を固定する。
方針：fat join の貼り合わせの左因子の計算。
規約：左図式は p。使われ方：普遍性の固定条件。 -/
lemma laxCosliceUncurry_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ laxCosliceUncurry f = p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：uncurry の右因子での値は普遍族の右端の評価。
方針：貼り合わせの右因子の計算。
規約：パラメーターを保つ。使われ方：curry との逆則。 -/
lemma laxCosliceUncurry_inr {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A ≫ laxCosliceUncurry f =
      laxCosliceRightInput A K ≫ uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 概要：uncurry の円柱での値は普遍族の円柱での評価。
方針：貼り合わせの円柱の計算。
規約：区間の座標を保つ。使われ方：curry との逆則。 -/
lemma laxCosliceUncurry_cylinder {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K A ≫ laxCosliceUncurry f =
      laxCosliceCylinderInput A K ≫ uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
