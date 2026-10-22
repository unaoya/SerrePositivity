module
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 前向き比較と元の逆律による組み立て成分の移送
概要：二つの組み立て四角形と元の片側逆律から境界段の成分を比較する。
方針：指定した逆律を挿入し、二つの比較四角形を順に合成する。
規約：全て点つき射の成分の等号。使われ方：旧 SOA K 構造射と実 BF 構造射の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra.PointedMapping

/-- 元の片側逆律と二つの比較四角形は、境界段上の組み立て成分を移す。 -/
lemma pointedComponentAssemblyTransfer
    {U B U' B' K V W T : PointedSimplicialSet.{u}}
    (q : U ⟶ B) (g : B ⟶ U) (α : U ⟶ U') (β : B ⟶ B') (q' : U' ⟶ B')
    (c : B' ⟶ K) (s : K ⟶ T) (a : U ⟶ V) (a' : U' ⟶ W)
    (δ : V ⟶ W) (d : W ⟶ T)
    (hi : componentOf (g ≫ q) = componentOf (𝟙 B))
    (hq : componentOf (α ≫ q') = componentOf (q ≫ β))
    (ha : componentOf (α ≫ a') = componentOf (a ≫ δ))
    (hs : componentOf ((q' ≫ c) ≫ s) = componentOf (a' ≫ d)) :
    componentOf (β ≫ c ≫ s) = componentOf ((g ≫ a) ≫ δ ≫ d) := by
  calc
    componentOf (β ≫ c ≫ s) = componentOf (g ≫ q ≫ β ≫ c ≫ s) := by
      simpa only [Category.assoc, Category.id_comp] using
        (componentOf_comp_right hi (β ≫ c ≫ s)).symm
    _ = componentOf (g ≫ α ≫ q' ≫ c ≫ s) := by
      simpa only [Category.assoc] using
        (componentOf_comp_left (componentOf_comp_right hq (c ≫ s)) g).symm
    _ = componentOf (g ≫ α ≫ a' ≫ d) := by
      simpa only [Category.assoc] using componentOf_comp_left hs (g ≫ α)
    _ = componentOf ((g ≫ a) ≫ δ ≫ d) := by
      simpa only [Category.assoc] using
        componentOf_comp_right (componentOf_comp_left ha g) d

end SerrePositivity.KST.SConstruction
