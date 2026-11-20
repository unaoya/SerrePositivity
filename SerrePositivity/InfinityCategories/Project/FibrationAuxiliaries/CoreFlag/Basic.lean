module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreProduct

/-!
概要：関手単体集合の core を並べた二重単体集合とその対角評価。
方針：標準単体の前合成を内部 Hom と core 関手で束ねる。
規約：外側は旗の次数、内側は可逆な自然変換の次数。
使われ方：Sp-8、一般 core 旗比較の入力と自然な評価射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- 標準単体を始域とする関手単体集合の二重単体集合。 -/
def functorDiagram (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  stdSimplex.op ⋙ internalHom ⋙ (evaluation SSet SSet).obj C

/-- `R(C)[m] = core Fun(Δ[m], C)`。構成自体は任意の単体集合に定義する。 -/
def resolution (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.functorDiagram C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 各行の対象は指定された関手単体集合の core そのもの。 -/
lemma resolution_obj (C : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution C).obj n =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (stdSimplex.obj n.unop)).obj C) : SSet.{u}) := rfl

/-- quasicategory の core 旗の各行は Kan 複体。 -/
instance resolution_obj_kanComplex (C : SSet.{u}) [Quasicategory C]
    (n : SimplexCategoryᵒᵖ) : KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution C).obj n) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (stdSimplex.obj n.unop)).obj C) : SSet.{u})
  infer_instance

/-- 外側・内側の次数を一致させた core 旗の対角。 -/
def diagonal (C : SSet.{u}) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution C)

/-- core 旗の n 単体を二つの標準単体の対角で評価する。 -/
def counit (C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.diagonal C ⟶ C where
  app n := ↾fun s ↦ s.val.app n (𝟙 n) (stdSimplex.objEquiv.symm (𝟙 n.unop))
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro s
    change _ = C.map f (s.val.app n (𝟙 n) (stdSimplex.objEquiv.symm (𝟙 n.unop)))
    have h := ConcreteCategory.congr_hom (s.val.naturality f (𝟙 n))
      (stdSimplex.objEquiv.symm (𝟙 n.unop))
    change s.val.app m (f ≫ (𝟙 m))
      ((stdSimplex.map f.unop).app m (stdSimplex.objEquiv.symm (𝟙 m.unop))) = _
    dsimp at h ⊢
    simp only [Category.id_comp, Category.comp_id] at h ⊢
    rw [← h]
    congr 1

/-- 後合成は core 旗の二重単体集合の間の射を与える。 -/
def map {C D : SSet.{u}} (f : C ⟶ D) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution C ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution D where
  app n := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom (stdSimplex.obj n.unop)).map f)
  naturality {n m} g := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (pre_comm_ihom_map _ f)

/-- 後合成による対角上の作用。 -/
def diagonalMap {C D : SSet.{u}} (f : C ⟶ D) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.diagonal C ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.diagonal D :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (Functor.uncurry.map (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.map f))

/-- 対角評価は標的の関手による後合成と可換。 -/
@[reassoc]
lemma counit_naturality {C D : SSet.{u}} (f : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.diagonalMap f ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.counit D = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.counit C ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- パラメーター方向に定値な関手単体。旗方向の単体は保持する。 -/
def constantSimplex {C : SSet.{u}} {n m : SimplexCategoryᵒᵖ} (s : C.obj n) :
    ((ihom (stdSimplex.obj n.unop)).obj C).obj m :=
  Functor.HomObj.ofNatTrans (SSet.yonedaEquiv.symm s)

/-- パラメーター方向が定値なら内部 Hom の core に入る。 -/
lemma constantSimplex_mem {C : SSet.{u}} {n m : SimplexCategoryᵒᵖ} (s : C.obj n) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.constantSimplex s ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (stdSimplex.obj n.unop)).obj C)).obj m := by
  intro f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_degenerate
    (X := (ihom (stdSimplex.obj n.unop)).obj C)
    (Functor.HomObj.ofNatTrans (SSet.yonedaEquiv.symm s))

/-- 元の旗を保持し、第二の単体方向には定値な対角包含。 -/
def inclusion (C : SSet.{u}) : C ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.diagonal C where
  app n := ↾fun s ↦ ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.constantSimplex s, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.constantSimplex_mem s⟩
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Functor.functorHom_ext
    intro d g
    apply ConcreteCategory.hom_ext
    intro x
    change C.map (stdSimplex.objEquiv x).op (C.map f s) =
      C.map (stdSimplex.objEquiv ((stdSimplex.map f.unop).app d x)).op s
    have hc := C.map_comp_apply f (stdSimplex.objEquiv x).op s
    dsimp at hc ⊢
    rw [← hc]
    congr 2

/-- 対角包含の後で対角評価をすると元の単体に戻る。 -/
@[reassoc (attr := simp)]
lemma inclusion_counit (C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.inclusion C ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.counit C = 𝟙 C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change C.map (𝟙 n) s = s
  exact C.map_id_apply n s

/-- 定数包含も標的の関手による後合成と可換。 -/
@[reassoc]
lemma inclusion_naturality {C D : SSet.{u}} (f : C ⟶ D) :
    f ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.inclusion D = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.inclusion C ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.diagonalMap f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Functor.functorHom_ext
  intro d g
  apply ConcreteCategory.hom_ext
  intro x
  exact (NatTrans.naturality_apply f (stdSimplex.objEquiv x).op s).symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
