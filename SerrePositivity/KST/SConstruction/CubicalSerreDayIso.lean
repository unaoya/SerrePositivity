module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayInverse
public import SerrePositivity.KST.SConstruction.CubicalSerreDayNaturality

/-! # 全 cubical sets 上の元の Day 鎖比較の同型性
概要：全 Day tensor 上の元の鎖比較を、実際の二変数自然同型として与える。
方針：独立な両 cell の tensor と連結 cell の二つの射の判定で両逆律を証明する。
規約：順射も逆射も元の cell 比較を保持。使われ方：Serre 鎖の強モノイダル構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Day 比較と組み立てから作った逆射の左逆律。 -/
lemma cubicalSerreDayComparison_inverse (K L : CubicalSet.{u}) :
    cubicalSerreDayComparison A K L ≫ cubicalSerreDayInverse A K L =
      𝟙 ((cubicalSerreChains A).obj (cubicalDayTensor K L)) := by
  apply cubicalSerreDay_hom_ext
  intro c d x y
  rw [← Category.assoc, cubicalSerreDayComparison_cell, Category.comp_id]
  dsimp only [cubicalSerreDayPair]
  rw [Category.assoc, cubicalSerreDayInverse_cell, cubicalSerreDayAssembly_cotensorator]

/-- 元の全ての独立な両 cell で検証した逆射の右逆律。 -/
lemma cubicalSerreDayInverse_comparison (K L : CubicalSet.{u}) :
    cubicalSerreDayInverse A K L ≫ cubicalSerreDayComparison A K L =
      𝟙 ((cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L) := by
  apply cubicalSerreTensor_hom_ext
  intro c d x y
  dsimp only [cubicalSerreCellTensor]
  rw [← Category.assoc, cubicalSerreDayInverse_cell,
    cubicalSerreDayAssembly_comparison, Category.comp_id]

/-- 任意の両 cubical sets における元の Day 鎖比較の同型。 -/
def cubicalSerreDayIso (K L : CubicalSet.{u}) :
    (cubicalSerreChains A).obj (cubicalDayTensor K L) ≅
      (cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L where
  hom := cubicalSerreDayComparison A K L
  inv := cubicalSerreDayInverse A K L
  hom_inv_id := cubicalSerreDayComparison_inverse A K L
  inv_hom_id := cubicalSerreDayInverse_comparison A K L

/-- 全 cubical sets で元の Day 鎖比較は同型。 -/
instance cubicalSerreDayComparison_isIso (K L : CubicalSet.{u}) :
    IsIso (cubicalSerreDayComparison A K L) :=
  (cubicalSerreDayIso A K L).isIso_hom

/-- 全 cubical sets 上の元の Day 鎖比較の二変数自然同型。 -/
def cubicalSerreDayNatIso :
    cubicalDayTensorFunctor ⋙ cubicalSerreChains A ≅
      (cubicalSerreChains A).prod (cubicalSerreChains A) ⋙ tensor (Complex A) :=
  NatIso.ofComponents (fun X => cubicalSerreDayIso A X.1 X.2)
    (fun f => cubicalSerreDayComparison_naturality A f.1 f.2)

/-- 元の自然同型の成分の順射は、同じ元の Day 鎖比較。 -/
lemma cubicalSerreDayNatIso_hom (K L : CubicalSet.{u}) :
    (cubicalSerreDayNatIso A).hom.app (K, L) = cubicalSerreDayComparison A K L := rfl

/-- 元の自然同型の逆射は、両 cell の余極限から作った同じ組み立て。 -/
lemma cubicalSerreDayNatIso_inv (K L : CubicalSet.{u}) :
    (cubicalSerreDayNatIso A).inv.app (K, L) = cubicalSerreDayInverse A K L := rfl

/-- 元の全体の組み立ては、元の両 cubical sets の射について自然。 -/
lemma cubicalSerreDayInverse_naturality {K K' L L' : CubicalSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((cubicalSerreChains A).map f ⊗ₘ (cubicalSerreChains A).map g) ≫
        cubicalSerreDayInverse A K' L' =
      cubicalSerreDayInverse A K L ≫
        (cubicalSerreChains A).map (cubicalDayTensorMap f g) := by
  apply (cancel_mono (cubicalSerreDayComparison A K' L')).mp
  rw [Category.assoc, cubicalSerreDayInverse_comparison, Category.comp_id,
    Category.assoc, cubicalSerreDayComparison_naturality, ← Category.assoc,
    cubicalSerreDayInverse_comparison, Category.id_comp]

end SerrePositivity.KST.SConstruction
