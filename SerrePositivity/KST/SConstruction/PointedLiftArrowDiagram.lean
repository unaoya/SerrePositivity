module
public import SerrePositivity.KST.SConstruction.AssemblyInputArrows
public import SerrePositivity.KST.SConstruction.PointedLiftTransportLaws

/-! # 全入力射上の持ち上げ選択空間の厳密な図式
概要：自然な射影の持ち上げ空間を入力の両側合成に関する関手へ束ねる。
方針：射影の自然性と持ち上げの移送の関手法則を使う。
規約：底の射を全単体で厳密に固定する。
使われ方：全入力射列にわたる比較逆射の coherent な選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra.PointedMapping

/-- 一つの入力射を自然な射影へ持ち上げる全選択空間。 -/
def pointedLiftArrowSpace {J : Type v} [Category.{w} J]
    {E B : J ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) (x : AssemblyInputArrow J) : SSet.{u} :=
  pointedLiftSpace (p.app (assemblyArrowTarget x)) (B.map (assemblyArrowHom x))

/-- 両側合成で移した底の射は次の入力射そのもの。 -/
lemma pointedLiftArrow_base {J : Type v} [Category.{w} J]
    (B : J ⥤ PointedSimplicialSet.{u}) {x y : AssemblyInputArrow J} (h : x ⟶ y) :
    B.map (assemblyArrowPre h) ≫ B.map (assemblyArrowHom x) ≫ B.map (assemblyArrowPost h) =
      B.map (assemblyArrowHom y) := by
  rw [← Functor.map_comp, ← Functor.map_comp, assemblyArrow_comm]

/-- 入力の両側合成を全持ち上げパラメーターへ作用させる。 -/
def pointedLiftArrowMap {J : Type v} [Category.{w} J]
    {E B : J ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B)
    {x y : AssemblyInputArrow J} (h : x ⟶ y) :
    pointedLiftArrowSpace p x ⟶ pointedLiftArrowSpace p y :=
  pointedLiftTransport _ _ _ _ (B.map (assemblyArrowPre h))
    (E.map (assemblyArrowPost h)) (B.map (assemblyArrowPost h))
    (p.naturality (assemblyArrowPost h)) (pointedLiftArrow_base B h)

/-- 恒等入力の移送は全持ち上げ選択空間の恒等射。 -/
lemma pointedLiftArrowMap_id {J : Type v} [Category.{w} J]
    {E B : J ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) (x : AssemblyInputArrow J) :
    pointedLiftArrowMap p (𝟙 x) = 𝟙 _ := by
  have hB : B.map (assemblyArrowPre (𝟙 x)) = 𝟙 (B.obj (assemblyArrowSource x)) := B.map_id _
  have hE : E.map (assemblyArrowPost (𝟙 x)) = 𝟙 (E.obj (assemblyArrowTarget x)) := E.map_id _
  apply pullback.hom_ext
  · dsimp only [pointedLiftArrowMap]
    rw [pointedLiftTransport_projection, Category.id_comp]
    have hm : pointedMappingTransport (B.map (assemblyArrowPre (𝟙 x)))
        (E.map (assemblyArrowPost (𝟙 x))) = 𝟙 _ := by
      rw [hB, hE]
      exact pointedMappingTransport_id _ _
    rw [hm, Category.comp_id]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 両側合成による持ち上げの移送は入力射の圏の合成を厳密に保つ。 -/
lemma pointedLiftArrowMap_comp {J : Type v} [Category.{w} J]
    {E B : J ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B)
    {x y z : AssemblyInputArrow J} (h : x ⟶ y) (k : y ⟶ z) :
    pointedLiftArrowMap p (h ≫ k) = pointedLiftArrowMap p h ≫ pointedLiftArrowMap p k := by
  apply pullback.hom_ext
  · dsimp only [pointedLiftArrowMap]
    rw [pointedLiftTransport_projection, Category.assoc, pointedLiftTransport_projection,
      ← Category.assoc, pointedLiftTransport_projection, Category.assoc, pointedMappingTransport_comp]
    simp only [assemblyArrowPre_comp, assemblyArrowPost_comp, Functor.map_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 全入力射と両側合成にわたる持ち上げ選択空間の厳密な関手。 -/
def pointedLiftArrowDiagram {J : Type v} [Category.{w} J]
    {E B : J ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) : AssemblyInputArrow J ⥤ SSet.{u} where
  obj := pointedLiftArrowSpace p
  map := pointedLiftArrowMap p
  map_id := pointedLiftArrowMap_id p
  map_comp := pointedLiftArrowMap_comp p

/-- 各射影が任意の単射への RLP を持てば、全入力射の持ち上げ選択空間は可縮 Kan。 -/
lemma pointedLiftArrowSpace_isContractibleKan {J : Type v} [Category.{w} J]
    {E B : J ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B)
    (hp : ∀ x, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app x).right)
    (x : AssemblyInputArrow J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (pointedLiftArrowSpace p x) :=
  pointedLiftSpace_isContractibleKan _ (hp _) _

end SerrePositivity.KST.SConstruction
