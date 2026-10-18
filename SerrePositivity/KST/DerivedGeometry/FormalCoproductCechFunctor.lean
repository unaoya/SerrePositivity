module

public import SerrePositivity.KST.DerivedGeometry.OpenCechIntersection

/-!
概要：有限積保存関手と形式的余積の Čech 対象の比較。
方針：各交叉の標準の積比較同型を全ての単体射について自然に束ねる。
規約：添字族の有限性は要求しない。
使われ方：TT §3、Toën §3.2 の表現可能前層による自由 Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u v a b
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type a} [Category.{b} D] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteProducts F] (U : FormalCoproduct.{w} C)

/--
概要：形式的余積の Čech 対象への有限積保存関手の適用は像の Čech 対象と同型。
方針：各積の比較同型を用い、各射影で単体射との自然性を検証する。
規約：全次数の余面・退化写像と両立する。
使われ方：TT §3、Toën §3.2 の自由 Čech 複体の局所収縮。
-/
def formalCoproductCechFunctorIso :
    U.cech ⋙ formalCoproductMapFunctor F ≅ ((formalCoproductMapFunctor F).obj U).cech :=
  NatIso.ofComponents
    (fun _ => FormalCoproduct.isoOfComponents (Equiv.refl _)
      (fun i => PreservesProduct.iso F (U.obj ∘ i)))
    (by
      intro n m f
      refine FormalCoproduct.hom_ext rfl ?_
      intro i
      dsimp [FormalCoproduct.isoOfComponents, FormalCoproduct.cech,
        FormalCoproduct.mapPower, formalCoproductMapFunctor]
      apply Pi.hom_ext
      intro j
      simp only [Category.id_comp, Category.comp_id, Category.assoc,
        PreservesProduct.iso_hom, Pi.lift_comp_π]
      refine (congrArg (fun k => F.map _ ≫ k) (piComparison_comp_π F _ j)).trans ?_
      refine (F.map_comp _ _).symm.trans ?_
      refine (congrArg F.map (Pi.lift_comp_π _ j)).trans ?_
      exact (piComparison_comp_π F _ _).symm)

end SerrePositivity.KST.DerivedGeometry
