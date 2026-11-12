module
public import SerrePositivity.KST.SConstruction.AssemblyInputArrows
public import SerrePositivity.KST.SConstruction.PointedExtensionTransportLaws

/-! # 全入力射上の延長選択空間の厳密な図式
概要：入力の両側合成に混合延長の全単体を作用させ、関手へ束ねる。
方針：自然変換の可換条件と延長の移送の関手法則を使う。
規約：零単体を選ばず、前後合成と恒等・合成を厳密に保持する。
使われ方：三本以上の入力射列に沿う coherent な延長選択の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra.PointedMapping
open SerrePositivity.InfinityCategories

/-- 一つの入力射に対応する、元の射を厳密に延長する全選択空間。 -/
def pointedExtensionArrowSpace {J : Type v} [Category.{w} J]
    {R A L : J ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    (x : AssemblyInputArrow J) : SSet.{u} :=
  pointedExtensionSpace (η.app (assemblyArrowSource x))
    (R.map (assemblyArrowHom x) ≫ θ.app (assemblyArrowTarget x))

/-- 両側合成は元の制限射と厳密に整合する。 -/
lemma pointedExtensionArrow_restriction {J : Type v} [Category.{w} J]
    {R L : J ⥤ PointedSimplicialSet.{u}} (θ : R ⟶ L)
    {x y : AssemblyInputArrow J} (h : x ⟶ y) :
    R.map (assemblyArrowPre h) ≫
        (R.map (assemblyArrowHom x) ≫ θ.app (assemblyArrowTarget x)) ≫
        L.map (assemblyArrowPost h) =
      R.map (assemblyArrowHom y) ≫ θ.app (assemblyArrowTarget y) := by
  calc
    _ = R.map (assemblyArrowPre h) ≫ R.map (assemblyArrowHom x) ≫
        R.map (assemblyArrowPost h) ≫ θ.app (assemblyArrowTarget y) := by
      simp only [Category.assoc, ← θ.naturality (assemblyArrowPost h)]
    _ = R.map (assemblyArrowPre h ≫ assemblyArrowHom x ≫ assemblyArrowPost h) ≫
        θ.app (assemblyArrowTarget y) := by simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [assemblyArrow_comm]

/-- 入力の両側合成を全延長パラメーターへ作用させる。 -/
def pointedExtensionArrowMap {J : Type v} [Category.{w} J]
    {R A L : J ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    {x y : AssemblyInputArrow J} (h : x ⟶ y) :
    pointedExtensionArrowSpace η θ x ⟶ pointedExtensionArrowSpace η θ y :=
  pointedExtensionTransport _ _ _ _ (R.map (assemblyArrowPre h))
    (A.map (assemblyArrowPre h)) (L.map (assemblyArrowPost h))
    (η.naturality (assemblyArrowPre h)) (pointedExtensionArrow_restriction θ h)

/-- 恒等入力の移送は全選択空間の恒等射。 -/
lemma pointedExtensionArrowMap_id {J : Type v} [Category.{w} J]
    {R A L : J ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    (x : AssemblyInputArrow J) : pointedExtensionArrowMap η θ (𝟙 x) = 𝟙 _ := by
  have hA : A.map (assemblyArrowPre (𝟙 x)) = 𝟙 (A.obj (assemblyArrowSource x)) := A.map_id _
  have hL : L.map (assemblyArrowPost (𝟙 x)) = 𝟙 (L.obj (assemblyArrowTarget x)) := L.map_id _
  apply pullback.hom_ext
  · dsimp only [pointedExtensionArrowMap]
    rw [pointedExtensionTransport_projection, Category.id_comp]
    have hm : pointedMappingTransport (A.map (assemblyArrowPre (𝟙 x)))
        (L.map (assemblyArrowPost (𝟙 x))) = 𝟙 _ := by
      rw [hA, hL]
      exact pointedMappingTransport_id _ _
    rw [hm, Category.comp_id]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 両側合成による移送は入力射の圏の合成を厳密に保つ。 -/
lemma pointedExtensionArrowMap_comp {J : Type v} [Category.{w} J]
    {R A L : J ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    {x y z : AssemblyInputArrow J} (h : x ⟶ y) (k : y ⟶ z) :
    pointedExtensionArrowMap η θ (h ≫ k) =
      pointedExtensionArrowMap η θ h ≫ pointedExtensionArrowMap η θ k := by
  apply pullback.hom_ext
  · dsimp only [pointedExtensionArrowMap]
    rw [pointedExtensionTransport_projection, Category.assoc,
      pointedExtensionTransport_projection, ← Category.assoc,
      pointedExtensionTransport_projection, Category.assoc, pointedMappingTransport_comp]
    simp only [assemblyArrowPre_comp, assemblyArrowPost_comp, Functor.map_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 全入力射とその両側合成にわたる、延長選択空間の厳密な関手。 -/
def pointedExtensionArrowDiagram {J : Type v} [Category.{w} J]
    {R A L : J ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L) :
    AssemblyInputArrow J ⥤ SSet.{u} where
  obj := pointedExtensionArrowSpace η θ
  map := pointedExtensionArrowMap η θ
  map_id := pointedExtensionArrowMap_id η θ
  map_comp := pointedExtensionArrowMap_comp η θ

/-- 各成分が anodyne な元の比較なら、全入力射の選択空間が可縮 Kan。 -/
lemma pointedExtensionArrowSpace_isContractibleKan {J : Type v} [Category.{w} J]
    {R A L : J ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    (hη : ∀ x, SSet.anodyneExtensions (η.app x).right)
    (x : AssemblyInputArrow J) [KanComplex (L.obj (assemblyArrowTarget x)).right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (pointedExtensionArrowSpace η θ x) :=
  pointedExtensionSpace_isContractibleKan _ (hη _) _

end SerrePositivity.KST.SConstruction
