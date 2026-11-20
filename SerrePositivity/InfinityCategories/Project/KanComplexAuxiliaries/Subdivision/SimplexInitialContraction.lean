module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismLastContraction

/-! # 標準単体の最初の頂点からの収縮
概要：標準単体の最初の頂点から恒等射への実際の prism を構成する。
方針：時刻零は最小元、時刻一は元の頂点を取る順序写像を使う。
規約：最初の頂点上で厳密に一定。使われ方：D(m,w) の零頂点への評価の自然同値。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：二点鎖と有限鎖から最小元と恒等射をつなぐ順序写像。
方針：時刻零で最小元、時刻一で第二成分。
規約：時刻は第一因子。使われ方：標準単体の零頂点からの prism。 -/
def simplexInitialOrder (n : ℕ) : Fin 2 × Fin (n + 1) →o Fin (n + 1) where
  toFun a := if a.1 = 0 then 0 else a.2
  monotone' {a b} h := by
    dsimp only
    split_ifs with ha hb hb
    · rfl
    · exact Fin.zero_le _
    · have ha' : a.1.val = 1 := by have := a.1.isLt; omega
      have hb' := h.1
      simp only [hb] at hb'
      have := Fin.le_iff_val_le_val.mp hb'
      simp only [Fin.val_zero] at this
      omega
    · exact h.2

/-- 概要：標準単体の零頂点から恒等射への単体的 prism。
方針：各単体の頂点列に最小元からの順序写像を合成する。
規約：区間は第一因子。使われ方：全同値図式の評価の比較。 -/
def simplexInitialContraction (n : ℕ) : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Δ[n] where
  app d := ↾fun s => stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialOrder n).comp
      ((stdSimplex.objEquiv s.1).toOrderHom.prod (stdSimplex.objEquiv s.2).toOrderHom)))
  naturality {d e} α := by
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨⟨e⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：零時刻での収縮は零頂点への定値射。
方針：零時刻の分岐を各単体で計算する。
規約：全次数での厳密等号。使われ方：定数図式への評価の合成。 -/
lemma simplexInitialContraction_zero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[n] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction n =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：一時刻での収縮は恒等射。
方針：一時刻の分岐を各単体で計算する。
規約：全次数での厳密等号。使われ方：評価の比較の恒等射側。 -/
lemma simplexInitialContraction_one (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[n] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction n = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：零頂点上では収縮全体がその頂点に定値。
方針：二つの時刻の分岐がともに零となることを計算する。
規約：頂点は Δ[0] からの実際の射。使われ方：評価の比較で零頂点を固定する式。 -/
lemma simplexInitialContraction_firstVertex (n : ℕ) :
    (Δ[1] ◁ SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction n = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  apply stdSimplex.ext
  intro i
  change (if _ = 0 then 0 else 0) = 0
  split_ifs <;> rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
