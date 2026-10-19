module
public import SerrePositivity.KST.SConstruction.MultiFixedSInterchange

/-! # 全多次数の S 交換の添字自然性
概要：任意の各方向の単体作用素が、全 gapped 図式の内外交換と厳密に可換。
方針：外側の一方向と残りの多方向を分け、交換の自然性を帰納的に合成する。
規約：対角に限定しない。使われ方：零方向の包含と交換の両立。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 独立な全多次数の射は固定 S_m の内外交換と厳密に可換。 -/
lemma multiFixedSEndofunctorIso_naturality (m r : ℕ)
    {d e : Fin r → SimplexCategoryᵒᵖ} (f : d ⟶ e) (X : StableModel.{u}) :
    ((multiSEndofunctor r).map f).app (sStableModel m X) ≫
        (multiFixedSEndofunctorIso m r e).hom.app X =
      (multiFixedSEndofunctorIso m r d).hom.app X ≫
        (sEndofunctor m).map (((multiSEndofunctor r).map f).app X) := by
  induction r with
  | zero =>
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (sEndofunctor m).map (𝟙 X)
    rw [CategoryTheory.Functor.map_id]
  | succ r ih =>
    let D := (multiSEndofunctor r).obj (fun i => d i.succ)
    let E := (multiSEndofunctor r).obj (fun i => e i.succ)
    let F := sEndofunctor (d 0).unop.len
    let G := sEndofunctor (e 0).unop.len
    let M := sEndofunctor m
    let a := simplicialStableEndofunctor.map (f 0)
    let t := (multiSEndofunctor r).map (fun i => f i.succ)
    let b := (multiFixedSEndofunctorIso m r (fun i => d i.succ)).hom.app X
    let c := (multiFixedSEndofunctorIso m r (fun i => e i.succ)).hom.app X
    let p := (sInterchangeStableIso (d 0).unop.len m (D.obj X)).hom
    let q := (sInterchangeStableIso (e 0).unop.len m (E.obj X)).hom
    let q' := (sInterchangeStableIso (e 0).unop.len m (D.obj X)).hom
    have ht : t.app (M.obj X) ≫ c = b ≫ M.map (t.app X) := ih (fun i => f i.succ)
    have ha : a.app (D.obj (M.obj X)) ≫ G.map b =
        F.map b ≫ a.app (M.obj (D.obj X)) := (a.naturality b).symm
    have hq : G.map (M.map (t.app X)) ≫ q = q' ≫ M.map (G.map (t.app X)) :=
      sInterchangeStableIso_naturality (e 0).unop.len m (t.app X)
    have hp : a.app (M.obj (D.obj X)) ≫ q' = p ≫ M.map (a.app (D.obj X)) :=
      Subtype.ext (sInterchange_outerMap m (D.obj X) (f 0).unop.toOrderHom)
    rw [multiFixedSEndofunctorIso_succ_app, multiFixedSEndofunctorIso_succ_app]
    change (a.app (D.obj (M.obj X)) ≫ G.map (t.app (M.obj X))) ≫ (G.map c ≫ q) =
      (F.map b ≫ p) ≫ M.map (a.app (D.obj X) ≫ G.map (t.app X))
    calc
      _ = a.app (D.obj (M.obj X)) ≫ G.map (t.app (M.obj X) ≫ c) ≫ q := by
        rw [G.map_comp]
        simp only [Category.assoc]
      _ = a.app (D.obj (M.obj X)) ≫ G.map (b ≫ M.map (t.app X)) ≫ q := by rw [ht]
      _ = (a.app (D.obj (M.obj X)) ≫ G.map b) ≫ G.map (M.map (t.app X)) ≫ q := by
        rw [G.map_comp]
        simp only [Category.assoc]
      _ = (F.map b ≫ a.app (M.obj (D.obj X))) ≫ G.map (M.map (t.app X)) ≫ q := by rw [ha]
      _ = F.map b ≫ a.app (M.obj (D.obj X)) ≫ q' ≫ M.map (G.map (t.app X)) := by
        simp only [Category.assoc]
        rw [hq]
      _ = F.map b ≫ p ≫ M.map (a.app (D.obj X)) ≫ M.map (G.map (t.app X)) := by
        rw [← Category.assoc (a.app (M.obj (D.obj X))), hp]
        simp only [Category.assoc]
      _ = _ := by rw [M.map_comp]; simp only [Category.assoc]

end SerrePositivity.KST.SConstruction
