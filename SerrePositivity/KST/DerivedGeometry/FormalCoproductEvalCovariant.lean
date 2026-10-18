module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：形式的余積の共変な評価と余積保存関手の適用の比較。
方針：標準の余積比較射を全ての形式的余積の射について自然に束ねる。
規約：任意の添字族について余積の保存を明示する。
使われ方：TT §3、Toën §3.2 の自由 Čech 鎖複体の切断評価。
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u v a b a' b'
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [HasCoproducts.{w} A]
  {B : Type a'} [Category.{b'} B] [HasCoproducts.{w} B]
  (F : C ⥤ A) (G : A ⥤ B)

/--
概要：関手適用後の形式的余積評価から評価後の関手適用への標準比較。
方針：各形式的余積で余積比較射を使い、挿入射で自然性を検証する。
規約：同型性は定義には要求しない。
使われ方：TT §3、Toën §3.2 の自由 Čech 評価。
-/
def formalCoproductEvalCovariantComparison :
    (FormalCoproduct.eval.{w} C B).obj (F ⋙ G) ⟶
      (FormalCoproduct.eval.{w} C A).obj F ⋙ G where
  app X := sigmaComparison G (fun i : X.I => F.obj (X.obj i))
  naturality {X Y} f := by
    apply Sigma.hom_ext
    intro i
    dsimp [FormalCoproduct.eval]
    simp only [Category.assoc, ι_comp_sigmaComparison, Sigma.ι_comp_desc,
      ι_comp_sigmaComparison_assoc, ← G.map_comp]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ sigmaComparison G (fun j : Y.I => F.obj (Y.obj j)))
      (Sigma.ι_comp_desc (fun j : X.I => G.map (F.map (f.φ j)) ≫
        Sigma.ι ((F ⋙ G).obj ∘ Y.obj) (f.f j)) i)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => G.map (F.map (f.φ i)) ≫ k)
      (ι_comp_sigmaComparison G (fun j : Y.I => F.obj (Y.obj j)) (f.f i))).trans ?_
    exact (G.map_comp _ _).symm

/--
概要：余積保存関手では共変な形式的余積評価の比較は同型。
方針：同じ余積の標準比較の同型性を使う。
規約：添字宇宙と同じ大きさの余極限の保存を要求する。
使われ方：TT §3、Toën §3.2 の自由加群と前層評価。
-/
instance formalCoproductEvalCovariantComparison_isIso
    [PreservesColimitsOfSize.{w, w} G] : IsIso (formalCoproductEvalCovariantComparison F G) := by
  have (X : FormalCoproduct.{w} C) :
      IsIso ((formalCoproductEvalCovariantComparison F G).app X) :=
    inferInstanceAs (IsIso (sigmaComparison G (fun i : X.I => F.obj (X.obj i))))
  exact NatIso.isIso_of_isIso_app _

/--
概要：余積保存関手は共変な形式的余積評価と自然に可換。
方針：証明済みの余積比較射の同型を逆向きに用いる。
規約：対象ごとの同型だけでなく全射との自然性を保持する。
使われ方：TT §3、Toën §3.2 の自由 Čech 鎖複体。
-/
def formalCoproductEvalCovariantIso [PreservesColimitsOfSize.{w, w} G] :
    (FormalCoproduct.eval.{w} C A).obj F ⋙ G ≅
      (FormalCoproduct.eval.{w} C B).obj (F ⋙ G) :=
  (asIso (formalCoproductEvalCovariantComparison F G)).symm

end SerrePositivity.KST.DerivedGeometry
