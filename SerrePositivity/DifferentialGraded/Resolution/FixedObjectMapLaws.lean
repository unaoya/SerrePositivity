module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapAugmentation

/-!
概要：固定対象増大の比較の恒等・合成と、同じ境界 cell 添字の厳密移送。
方針：元の Hom 写像をそのまま合成し、指定 cycle と原始元を同時に送る。
規約：模型・対象ラベル・増大を変更しない。
使われ方：D-8 e の同じ cell 分解上の比較の厳密則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E] {B : Type z} [DGCategory A B]

lemma map_ext {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {F : DGFunctor A D E}
    {M N : Map S T F} (h : M.hom = N.hom) : M = N := by
  cases M
  cases N
  cases h
  rfl

def identity (S : FixedObjectAugmentation A D D id) : Map S S (DGFunctor.id D) where
  hom _ _ := 𝟙 _
  map_id _ := by rw [Category.comp_id]; rfl
  map_comp _ _ _ := by simp; rfl
  augmentation x y := by
    change 𝟙 _ ≫ S.map x y = S.map x y ≫ 𝟙 _
    simp

def composition {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {U : FixedObjectAugmentation A B B id}
    {F : DGFunctor A D E} {G : DGFunctor A E B} (M : Map S T F) (N : Map T U G) :
    Map S U (F.comp G) where
  hom x y := M.hom x y ≫ N.hom (F.obj x) (F.obj y)
  map_id x := by rw [← Category.assoc, M.map_id, N.map_id]; rfl
  map_comp x y z := by
    rw [← Category.assoc, M.map_comp, Category.assoc, N.map_comp,
      ← Category.assoc, ← tensorHom_comp_tensorHom]
    rfl
  augmentation x y := by
    change (M.hom x y ≫ N.hom (F.obj x) (F.obj y)) ≫
      U.map (G.obj (F.obj x)) (G.obj (F.obj y)) =
      S.map x y ≫ (F.map x y ≫ G.map (F.obj x) (F.obj y))
    rw [Category.assoc, N.augmentation, ← Category.assoc, M.augmentation, Category.assoc]

lemma identity_cellMap (S : FixedObjectAugmentation A D D id) (i : S.CellIndex) :
    (identity S).cellMap i = i := by
  rcases i with ⟨x, y, c⟩
  cases c
  rfl

lemma composition_cellMap {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {U : FixedObjectAugmentation A B B id}
    {F : DGFunctor A D E} {G : DGFunctor A E B} (M : Map S T F) (N : Map T U G)
    (i : S.CellIndex) : (composition M N).cellMap i = N.cellMap (M.cellMap i) := rfl

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
