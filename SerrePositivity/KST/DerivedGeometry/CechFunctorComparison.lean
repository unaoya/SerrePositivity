module

public import SerrePositivity.KST.DerivedGeometry.FormalCoproductEvalComparison

/-!
概要：加法的な有限積保存関手と有限被覆の Čech 複体の比較同型。
方針：余単体対象の積比較を交代余面複体へ移す。
規約：各項の同型だけでなく微分との両立を証明する。
使われ方：TT §3、Toën §3.2 の基本開 Čech 複体の局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w a a' b b'
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type a} [Category.{b} A] [Preadditive A]
  {B : Type a'} [Category.{b'} B] [Preadditive B]
  (F : A ⥤ B) [F.Additive]

attribute [local simp] Functor.map_zsmul in
/--
概要：交代余面複体と加法的関手の適用は自然に可換。
方針：各項の恒等同型と微分の有限和・整数倍の保存を使う。
規約：交代符号を含む同じ微分を保持する。
使われ方：TT §3、Toën §3.2 の Čech 微分の局所化比較。
-/
def alternatingCofaceCompMapIso :
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙ F.mapHomologicalComplex (.up ℕ) ≅
      (CosimplicialObject.whiskering A B).obj F ⋙
        AlgebraicTopology.alternatingCofaceMapComplex B :=
  NatIso.ofComponents
    (fun X => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
      intro i j hij
      have hj : i + 1 = j := hij
      subst j
      simp [AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj,
        AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum,
        CosimplicialObject.δ]))
    (by
      intros X Y f
      ext n
      simp [AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.map])

variable {C : Type w} [Category.{v} C] [HasFiniteProducts C]
  [HasProducts.{u} A] [HasProducts.{u} B]
  {ι : Type u} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ A) [PreservesFiniteProducts F]

/--
概要：加法的な有限積保存関手を有限被覆の Čech 複体に適用すると適用後の Čech 複体と同型。
方針：交代余面複体の自然比較と有限積の余単体比較を合成する。
規約：全次数・微分を同時に比較し、切り詰めはしない。
使われ方：TT §3、Toën §3.2 の有限基本開被覆の局所化後の完全性。
-/
def finiteCechFunctorIso :
    (F.mapHomologicalComplex (.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ F) :=
  (alternatingCofaceCompMapIso F).app
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex B).mapIso
      (asIso (cechCosimplicialComparison P F U))

end SerrePositivity.KST.DerivedGeometry
