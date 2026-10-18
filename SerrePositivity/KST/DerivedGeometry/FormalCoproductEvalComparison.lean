module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：形式的余積の前層による評価と関手の適用の積比較。
方針：積の標準比較写像を形式的余積の射について自然に束ねる。
規約：同型性は有限な添字と有限積保存のもとで証明する。
使われ方：TT §3、Toën §3.2 の有限 Čech 複体の各項の局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w a a' b b'
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type w} [Category.{v} C]
  {A : Type a} [Category.{b} A] [HasProducts.{u} A]
  {B : Type a'} [Category.{b'} B] [HasProducts.{u} B]
  (P : Cᵒᵖ ⥤ A) (F : A ⥤ B)

/--
概要：形式的余積の評価後に関手を適用するものから適用後の評価への自然比較。
方針：各対象で積の標準比較写像を使い、射影で自然性を検証する。
規約：関手が積を保つことは定義には不要。
使われ方：TT §3、Toën §3.2 の Čech 局所化の各項と微分の比較。
-/
def formalCoproductEvalComparison :
    (FormalCoproduct.evalOp.{u} C A).obj P ⋙ F ⟶
      (FormalCoproduct.evalOp.{u} C B).obj (P ⋙ F) where
  app X := piComparison F (fun i : X.unop.I => P.obj (.op (X.unop.obj i)))
  naturality {X Y} f := by
    apply Pi.hom_ext
    intro i
    dsimp [FormalCoproduct.evalOp]
    simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π,
      piComparison_comp_π_assoc, ← F.map_comp]

/--
概要：有限な形式的余積では有限積保存関手の評価比較は同型。
方針：同じ有限積の標準比較の同型性を使う。
規約：任意の添字宇宙の有限性を認める。
使われ方：TT §3、Toën §3.2 の有限基本開 Čech 各項。
-/
instance formalCoproductEvalComparison_isIso [PreservesFiniteProducts F]
    (X : (FormalCoproduct.{u} C)ᵒᵖ) [Finite X.unop.I] :
    IsIso ((formalCoproductEvalComparison P F).app X) := by
  change IsIso (piComparison F (fun i : X.unop.I => P.obj (.op (X.unop.obj i))))
  infer_instance

variable [HasFiniteProducts C] {ι : Type u} (U : ι → C)

/--
概要：Čech 余単体対象の評価と関手の適用の自然比較。
方針：形式的余積の評価比較に同じ Čech 対象を前合成する。
規約：Čech 各次数と全ての余面・余退化写像を同時に比較する。
使われ方：TT §3、Toën §3.2 の Čech 微分の局所化。
-/
def cechCosimplicialComparison :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P) ⋙ F ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj (P ⋙ F) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (FormalCoproduct.mk ι U).cech.rightOp
      (formalCoproductEvalComparison P F)

/--
概要：有限被覆と有限積保存関手の Čech 余単体比較は同型。
方針：各次数の添字関数の型も有限であることを使う。
規約：各次数を切り詰めない。
使われ方：TT §3、Toën §3.2 の非有界 Čech 計算の各行。
-/
instance cechCosimplicialComparison_isIso [Finite ι] [PreservesFiniteProducts F] :
    IsIso (cechCosimplicialComparison P F U) := by
  have (n : SimplexCategory) : IsIso ((cechCosimplicialComparison P F U).app n) := by
    change IsIso (𝟙 _ ≫ piComparison F
      (fun i : (ToType n → ι) => P.obj (.op (∏ᶜ (U ∘ i)))))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end SerrePositivity.KST.DerivedGeometry
