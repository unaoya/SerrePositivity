module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexConeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexLimitReflection
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectiveInvertedHom
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalObjectLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Definition

/-!
概要：反映された同型閉な全部分圏の小極限を周囲の元の極限から構成する。
方針：反映像を局所対象として認識し、局所対象の極限閉性と全錐の持ち上げを使う。
規約：元の図式・極限錐を保持し、反映関手自体の極限保存は要求しない。
使われ方：余完備な Ind 模型と presentable 圏の全小極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：周囲の極限頂点が所属すれば元の全部分図式の極限が存在する。
方針：同じ全錐を持ち上げ、周囲の極限性を反映する。
規約：形状は任意の単体集合。
使われ方：極限閉性から native な極限存在への接続。 -/
lemma fullSubcomplex_hasLimit_of_apex {K X : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (D : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (c : JoinCone (D ≫ (fullSubcomplexOnVertices X P).ι))
    (hc : IsLimitCone c) (hp : P c.vertex) : HasLimit D := by
  refine ⟨fullSubcomplexConeLift P D c hp, ?_⟩
  apply isLimitCone_of_fullSubcomplex P
  rw [fullSubcomplexConeLift_inclusion]
  exact hc

/-- 概要：反映部分圏からの図式の周囲の極限は局所対象。
方針：包含の像の局所性を反映が反転する辺集合の局所性へ移す。
規約：P の同型不変性も反映の極限保存も要求しない。
使われ方：同型閉な反映像の極限閉性。 -/
lemma reflective_isLocal_limitCone {K X : SSet.{u}} [Quasicategory X]
    {P : X _⦋0⦌ → Prop} (r : ReflectiveSubcategory X P)
    (D : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (c : JoinCone (D ≫ (fullSubcomplexOnVertices X P).ι)) (hc : IsLimitCone c) :
    r.IsLocal c.vertex := by
  apply (reflective_isLocal_iff_invertedEdges r c.vertex).mpr
  apply isLocalObject_limitCone (invertedEdges r.reflector) c hc
  intro k
  exact (reflective_isLocal_iff_invertedEdges r _).mp (r.isLocal_inclusion (D.app _ k))

/-- 概要：同型閉な反映像は周囲の任意の極限で閉じる。
方針：極限の局所性から反映像の対象との同型を取り、所属を移す。
規約：元の極限頂点への所属を結論する。
使われ方：小極限の全錐を反映部分圏へ戻す。 -/
lemma reflective_mem_limitCone {K X : SSet.{u}} [Quasicategory X]
    {P : X _⦋0⦌ → Prop} (r : ReflectiveSubcategory X P)
    (hP : ∀ {x y : X _⦋0⦌}, VertexIso x y → P x → P y)
    (D : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (c : JoinCone (D ≫ (fullSubcomplexOnVertices X P).ι)) (hc : IsLimitCone c) :
    P c.vertex := by
  obtain ⟨y, ⟨e⟩⟩ := (r.isLocal_iff_essentialImage c.vertex).mp
    (reflective_isLocal_limitCone r D c hc)
  exact hP e (fullSubcomplexOnVertices_vertex y)

/-- 概要：完備な圏の同型閉な反映全部分圏は全小極限を持つ。
方針：元の周囲の極限を取り、局所性による所属と全錐の持ち上げを使う。
規約：小形状は宇宙 u、周囲と部分圏は u+1。
使われ方：presentable 圏の小極限存在定理。 -/
lemma reflectiveSubcategory_hasSmallLimits {X : SSet.{u + 1}} [Quasicategory X]
    {P : X _⦋0⦌ → Prop} (r : ReflectiveSubcategory X P)
    (hP : ∀ {x y : X _⦋0⦌}, VertexIso x y → P x → P y)
    (hX : HasSmallLimits X) : HasSmallLimits (fullSubcomplexOnVertices X P : SSet.{u + 1}) := by
  intro K D
  obtain ⟨c, hc⟩ := hX K (D ≫ (fullSubcomplexOnVertices X P).ι)
  exact fullSubcomplex_hasLimit_of_apex P D c hc (reflective_mem_limitCone r hP D c hc)

end SerrePositivity.InfinityCategories.F2.Presentable
