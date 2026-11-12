module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismFinalBoundary

/-!
概要：標準単体の最後の頂点への prism による収縮。
方針：時刻零は元の頂点、時刻一は最後の頂点を取る単調写像を用いる。
規約：時刻零が恒等射、時刻一が最後の頂点に定値。
使われ方：Kerodon §7.1.5（Tag 02WE） の fiber の終対象への輸送。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：二点鎖と有限鎖の積を最後の頂点へ収縮する単調写像。
方針：時刻零では第二成分、時刻一では最後の頂点を取る。
規約：恒等射から最後の頂点への辺。
使われ方：Kerodon §7.1.5（Tag 02WE） の基底の収縮。 -/
def prismLastOrderHom (n : ℕ) : Fin 2 × Fin (n + 1) →o Fin (n + 1) where
  toFun a := if a.1 = 0 then a.2 else Fin.last n
  monotone' {a b} h := by
    dsimp only
    split_ifs with ha hb hb
    · exact h.2
    · exact Fin.le_last _
    · have ha' : a.1.val = 1 := by have := a.1.isLt; omega
      have hb' := h.1
      simp only [hb] at hb'
      have := Fin.le_iff_val_le_val.mp hb'
      simp only [Fin.val_zero] at this
      omega
    · rfl

/-- 概要：最後の頂点への収縮を単体集合の射として表す。
方針：各単体の頂点列に単調な収縮を合成する。
規約：tensor は単体集合の直積。
使われ方：Kerodon §7.1.5（Tag 02WE） の相対終対象の基底の prism。 -/
def prismLastContraction (n : ℕ) : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Δ[n] where
  app d := ↾fun s ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    ((prismLastOrderHom n).comp
      ((stdSimplex.objEquiv s.1).toOrderHom.prod (stdSimplex.objEquiv s.2).toOrderHom)))
  naturality {d e} α := by
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨⟨e⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：最後の頂点への収縮の先頭は恒等射。
方針：時刻零の分岐を計算する。
規約：すべての次元で成立。
使われ方：Kerodon §7.1.5（Tag 02WE） の元の境界の固定。 -/
lemma prismLastContraction_zero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[n] : SSet.{u}) ≫ prismLastContraction n = 𝟙 Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：最後の頂点への収縮の終端は最後の頂点に定値。
方針：時刻一の分岐を計算する。
規約：零次元も許す。
使われ方：Kerodon §7.1.5（Tag 02WE） の輸送先の fiber の指定。 -/
lemma prismLastContraction_one (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[n] : SSet.{u}) ≫ prismLastContraction n =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：最後の頂点上の垂直辺は収縮によって最後の頂点に定値。
方針：二つの時刻での有限順序写像の値を計算する。
規約：境界の最後の頂点を含めた辺を用いる。
使われ方：Kerodon §7.1.5（Tag 02WE） の終点の垂直辺の固定。 -/
lemma prismBoundaryLastVerticalEdge_contraction (n : ℕ) :
    ((Δ[1] ◁ (boundary (n + 1)).ι) ≫ prismLastContraction (n + 1)).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismBoundaryLastVerticalEdge n) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) 1 := by
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 概要：最後の頂点の上では prism の収縮全体が最後の頂点に定値。
方針：時間の二つの分岐が同じ最後の頂点を取ることを計算する。
規約：標準頂点を Δ[0] からの Yoneda 射で指定する。
使われ方：Kerodon §7.1.5（Tag 02WE） の終対象の頂点を固定した輸送。 -/
lemma prismLastContraction_lastVertex (n : ℕ) :
    (Δ[1] ◁ SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n))) ≫
      prismLastContraction n = SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  apply stdSimplex.ext
  intro i
  change (if _ = 0 then Fin.last n else Fin.last n) = Fin.last n
  split_ifs <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
