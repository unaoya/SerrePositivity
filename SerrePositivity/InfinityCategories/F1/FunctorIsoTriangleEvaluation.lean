module

public import SerrePositivity.InfinityCategories.F1.IsoTriangleIdentity
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-!
概要：指定関手同型の三角等式を同じ頂点の成分へ写す。
方針：ホモトピー評価関手による同型の像の合成則を使う。
規約：元の指定同型の成分を選び直さない。
使われ方：共有セルでの成分 path の整合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ指定関手同型の成分は合成を保つ。 -/
lemma FunctorIso.app_trans {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {a b t : X ⟶ Y} (e : FunctorIso a b) (k : FunctorIso b t) (x : X _⦋0⦌) :
    FunctorIso.app (e ≪≫ k) x = FunctorIso.app e x ≪≫ FunctorIso.app k x := by
  have hn : FunctorIso.toNatIso (e ≪≫ k) = e.toNatIso ≪≫ k.toNatIso := by
    simp only [FunctorIso.toNatIso, Functor.mapIso_trans, Iso.trans_assoc,
      Iso.self_symm_id_assoc]
  exact congrArg (fun v ↦ v.app (SSet.HomotopyCategory.mk x)) hn

/-- 元の指定三角等式は、同じ頂点での指定成分の三角等式を与える。 -/
lemma IsoTriangleCommutes.app {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {a b t : X ⟶ Y} {e : FunctorIso a b} {k : FunctorIso b t} {d : FunctorIso a t}
    (h : IsoTriangleCommutes e k d) (x : X _⦋0⦌) : e.app x ≪≫ k.app x = d.app x := by
  exact (FunctorIso.app_trans e k x).symm.trans
    (congrArg (fun v : FunctorIso a t ↦ v.app x) h)

end SerrePositivity.InfinityCategories
