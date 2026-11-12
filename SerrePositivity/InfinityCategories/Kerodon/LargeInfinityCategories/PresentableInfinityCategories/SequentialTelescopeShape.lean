module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightMapMono
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：可算列の各隣接辺を、離散な端点に沿って貼る望遠鏡の形状を構成する。
方針：可算個の区間の nerve と可算離散頂点を、両端点の nerve に沿う pushout で貼る。
規約：同じ辺の始点を n、終点を n+1 に固定し、可算 nerve への全写像を保持する。
使われ方：P-11 の可算列の余積・pushout 表示。共終性と余極限性は後続工程。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：各隣接区間の両端点を、その区間の圏へ入れる。
方針：可算番号は離散成分、端点は二元の順序圏の対象として読む。
規約：区間間の射を追加しない。
使われ方：望遠鏡の形状 pushout の単射側。 -/
def sequentialTelescopeBoundaryFunctor :
    Discrete (ULift.{u} ℕ × Fin 2) ⥤ Discrete (ULift.{u} ℕ) × Fin 2 :=
  Discrete.functor (fun p ↦ (Discrete.mk p.1, p.2))

/-- 概要：区間番号 n の端点 i を、列の頂点 n+i へ貼り付ける。
方針：二つの端点の番号を自然数の和で統一する。
規約：隣接する二つの区間だけが同じ頂点を共有する。
使われ方：望遠鏡の形状 pushout の離散頂点側。 -/
def sequentialTelescopeAttachFunctor :
    Discrete (ULift.{u} ℕ × Fin 2) ⥤ Discrete (ULift.{u} ℕ) :=
  Discrete.functor (fun p ↦ Discrete.mk (ULift.up (p.1.down + p.2.val)))

/-- 概要：各区間を可算順序圏の同じ隣接辺へ写す。
方針：対象 (n,i) を n+i に写し、区間の順序射を対応する不等式へ送る。
規約：端点の像は厳密な対象の等式。
使われ方：望遠鏡全体から可算 nerve への射の区間側。 -/
def sequentialTelescopeIntervalFunctor :
    Discrete (ULift.{u} ℕ) × Fin 2 ⥤ ULift.{u} ℕ where
  obj p := ULift.up (p.1.as.down + p.2.val)
  map {p q} f := homOfLE (by
    have hn := Discrete.eq_of_hom f.1
    have hi := leOfHom f.2
    change p.1.as.down + p.2.val ≤ q.1.as.down + q.2.val
    rw [hn]
    exact Nat.add_le_add_left hi _)

/-- 概要：可算離散頂点を、同じ番号の順序圏の頂点へ入れる。
方針：対象は恒等に保つ離散圏の関手を使う。
規約：元の持ち上げた自然数を保持する。
使われ方：望遠鏡から可算 nerve への射の頂点側。 -/
def sequentialTelescopeVertexFunctor : Discrete (ULift.{u} ℕ) ⥤ ULift.{u} ℕ :=
  Discrete.functor id

/-- 概要：端点の貼り付けと可算列への射は、同じ関手の等式で整合する。
方針：対象の番号 n+i が等しく、順序圏の射は一意であることを使う。
規約：自然同型だけに弱めない。
使われ方：望遠鏡から可算 nerve への pushout 降下。 -/
lemma sequentialTelescopeFunctor_condition :
    sequentialTelescopeBoundaryFunctor.{u} ⋙ sequentialTelescopeIntervalFunctor =
      sequentialTelescopeAttachFunctor ⋙ sequentialTelescopeVertexFunctor := by
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 概要：両端点から区間の nerve への写像は単射。
方針：離散始域の忠実性と、区間番号・端点を保つ対象写像の単射性を使う。
規約：後続の形状 pushout に必要な単射性を明示する。
使われ方：保存された余極限の形状 pushout 接着。 -/
instance sequentialTelescopeBoundary_mono :
    Mono (nerveMap sequentialTelescopeBoundaryFunctor.{u}) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful
  intro p q h
  apply Discrete.ext
  change (Discrete.mk p.as.1, p.as.2) = (Discrete.mk q.as.1, q.as.2) at h
  exact Prod.ext (congrArg (fun r ↦ r.1.as) h)
    (congrArg (fun r : Discrete (ULift.{u} ℕ) × Fin 2 ↦ r.2) h)

/-- 概要：可算個の区間を同じ離散端点に沿って貼った望遠鏡の形状。
方針：端点の離散頂点への写像と区間への単射の pushout を取る。
規約：単体集合の形状であり、任意の標的圏の余極限は仮定しない。
使われ方：P-11 の可算列に対する余積と pushout の二段構成。 -/
def sequentialTelescopeShape : SSet.{u} :=
  pushout (nerveMap sequentialTelescopeAttachFunctor.{u})
    (nerveMap sequentialTelescopeBoundaryFunctor.{u})

/-- 概要：望遠鏡の各区間と各頂点を、元の可算 nerve へ写す。
方針：端点上の厳密な関手等式で二つの nerve 写像を pushout へ降ろす。
規約：元の列に前合成するための一つの全単体集合写像。
使われ方：可算列の元の全図式の望遠鏡への制限。 -/
def sequentialTelescopeToNerve : sequentialTelescopeShape.{u} ⟶ nerve (ULift.{u} ℕ) :=
  pushout.desc (nerveMap sequentialTelescopeVertexFunctor.{u})
    (nerveMap sequentialTelescopeIntervalFunctor.{u}) (by
      change nerveMap (sequentialTelescopeAttachFunctor.{u} ⋙
        sequentialTelescopeVertexFunctor.{u}) =
          nerveMap (sequentialTelescopeBoundaryFunctor.{u} ⋙
            sequentialTelescopeIntervalFunctor.{u})
      rw [sequentialTelescopeFunctor_condition])

/-- 概要：望遠鏡の頂点側の制限は、元の同じ離散頂点の包含。
方針：pushout の降下と包含の計算を使う。
規約：全 nerve 写像の等式。
使われ方：望遠鏡上の図式の余積頂点の識別。 -/
lemma sequentialTelescopeToNerve_vertices :
    pushout.inl (nerveMap sequentialTelescopeAttachFunctor.{u})
      (nerveMap sequentialTelescopeBoundaryFunctor) ≫ sequentialTelescopeToNerve =
        nerveMap sequentialTelescopeVertexFunctor.{u} := by
  exact pushout.inl_desc _ _ _

/-- 概要：望遠鏡の区間側の制限は、元の同じ隣接辺の族。
方針：pushout の降下と包含の計算を使う。
規約：全 nerve 写像の等式。
使われ方：元の可算列の隣接辺を回収する。 -/
lemma sequentialTelescopeToNerve_intervals :
    pushout.inr (nerveMap sequentialTelescopeAttachFunctor.{u})
      (nerveMap sequentialTelescopeBoundaryFunctor) ≫ sequentialTelescopeToNerve =
        nerveMap sequentialTelescopeIntervalFunctor.{u} := by
  exact pushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
