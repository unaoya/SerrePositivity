module

public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.RightPrism

/-!
概要：円柱の終点包含の right anodyne 性。
方針：最後の一次ホーンの切断が同型であることを示し、ホーンと単体集合の積の定理を使う。
規約：区間は左因子、終点は一。
使われ方：Kerodon Proposition 4.2.5.3、Proposition 5.2.4.5 の右錐への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の一次ホーンとの積への標準切断は同型。
方針：第二射影を逆射とし、ホーン内の単体の全頂点が一であることを検査する。
規約：A は任意の単体集合。
使われ方：Kerodon Proposition 4.2.5.3、円柱の終点と最後の一次ホーンの同定。 -/
noncomputable def hornOneLastSectionIso (A : SSet.{u}) :
    A ≅ (horn 1 1 : SSet.{u}) ⊗ A where
  hom := hornOneLastSection A
  inv := snd (horn 1 1 : SSet.{u}) A
  hom_inv_id := hornOneLastSection_snd A
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    apply Prod.ext
    · apply Subtype.ext
      apply stdSimplex.ext
      intro i
      change (1 : Fin 2) = a.val i
      apply Fin.ext
      have ha : a.val i ≠ 0 := by
        obtain ⟨j, hj, hm⟩ := (mem_horn_iff_notMem_range a.val (1 : Fin 2)).1 a.property
        have hjval : j.val ≠ 1 := by intro h; exact hj (Fin.ext h)
        have hj0 : j = 0 := Fin.ext (by change j.val = 0; have := j.isLt; omega)
        subst j
        intro h
        exact hm ⟨i, h⟩
      have hv : (a.val i).val ≠ 0 := by intro h; exact ha (Fin.ext h)
      change 1 = (a.val i).val
      have := (a.val i).isLt
      omega
    · rfl

/-- 概要：円柱の終点包含は right anodyne。
方針：同型な最後の一次ホーンの積の包含へ移す。
規約：区間の一端から Δ[1]×A への射。
使われ方：Kerodon Proposition 4.2.5.3、Proposition 5.2.4.5 の写像円柱の終域包含。 -/
lemma prismEndpoint_one_rightAnodyne (A : SSet.{u}) :
    rightAnodyneExtensions (prismEndpoint 1 A) := by
  rw [← hornOneLastSection_ι]
  change rightAnodyneExtensions ((hornOneLastSectionIso A).hom ≫ ((horn 1 1).ι ▷ A))
  rw [rightAnodyneExtensions.cancel_left_of_respectsIso]
  exact rightAnodyneExtensions_point_whiskerRight A

end SerrePositivity.InfinityCategories
