module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopower
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization

/-!
概要：余積frameの各挿入により、重み付きHomを要素圏へ制限する。
方針：積添字上の余積図式をcurryし、挿入の両方向の自然性を確認する。
使われ方：HTT 4.2.4.4、RR02(a)の要素圏での実現の表示。
規約：指定した重みを射影に沿って制限し、全単体で同じ射を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
namespace SerrePositivity.DiagramModel.ElementsCopower
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (F : K ⥤ Type w) (B : K ⥤ SimplexCategory ⥤ C)

/-- 同じ余積図式を余単体方向を含む積添字で構成する。 -/
def frames : K ⥤ SimplexCategory ⥤ C :=
  Functor.curry.obj (diagram (CategoryTheory.Prod.fst K SimplexCategory ⋙ F)
    (Functor.uncurry.obj B))

/-- 各要素が指定する、全余単体次数での余積の挿入。 -/
def summand (k : K) (x : F.obj k) : B.obj k ⟶ (frames F B).obj k where
  app n := Sigma.ι (fun _ : F.obj k => (B.obj k).obj n) x
  naturality n m f := by
    simp [frames, diagram, Category.assoc]

/-- 添字の射に沿って要素を移すと、同じ余積の挿入が得られる。 -/
lemma summand_naturality {k l : K} (f : k ⟶ l) (x : F.obj k) :
    B.map f ≫ summand F B l (F.map f x) =
      summand F B k x ≫ (frames F B).map f := by
  apply NatTrans.ext
  funext n
  simp [summand, frames, diagram, Category.assoc]

/-- 重み付きHomの射を各挿入に制限する、全要素・全単体の射。 -/
def weightedHomToElements (W : Kᵒᵖ ⥤ SSet.{w}) (Y : C)
    (a : W ⟶ (FrameWeightRealization.hom K (frames F B)).obj Y) :
    (Functor.Elements.π F).op ⋙ W ⟶
      (FrameWeightRealization.hom F.Elements (Functor.Elements.π F ⋙ B)).obj Y where
  app e := a.app (Opposite.op e.unop.obj) ≫
    (cosimplicialHomMap (summand F B e.unop.obj e.unop.val)).app Y
  naturality e e' f := by
    ext n z
    have h := ConcreteCategory.congr_hom
      (congr_app (a.naturality f.unop.hom.op) n) z
    change (a.app (Opposite.op e'.unop.obj)).app n
        ((W.map f.unop.hom.op).app n z) =
      ((frames F B).map f.unop.hom).app n.unop ≫
        (a.app (Opposite.op e.unop.obj)).app n z at h
    change (summand F B e'.unop.obj e'.unop.val).app n.unop ≫
        (a.app (Opposite.op e'.unop.obj)).app n
          ((W.map f.unop.hom.op).app n z) =
      (B.map f.unop.hom).app n.unop ≫
        ((summand F B e.unop.obj e.unop.val).app n.unop ≫
          (a.app (Opposite.op e.unop.obj)).app n z)
    have hs := congr_app (summand_naturality F B f.unop.hom e'.unop.val) n.unop
    rw [f.unop.map_val] at hs
    exact (congrArg (fun g =>
      (summand F B e'.unop.obj e'.unop.val).app n.unop ≫ g) h).trans (by
        simpa only [NatTrans.comp_app, Category.assoc] using
          congrArg (fun g => g ≫ (a.app (Opposite.op e.unop.obj)).app n z) hs.symm)

end SerrePositivity.DiagramModel.ElementsCopower
