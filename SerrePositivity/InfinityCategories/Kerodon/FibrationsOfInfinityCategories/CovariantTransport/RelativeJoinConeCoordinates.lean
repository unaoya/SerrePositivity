module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection

/-!
概要：標準単体の右錐の座標と頂点での比較の一意性。
方針：join の頂点を両因子の頂点に分け、標準単体への射の頂点による検出を使う。
規約：右錐の頂点は標準零単体、区間の新しい右頂点の時刻は一。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の右錐との比較の座標。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：join から標準単体への射は両因子への制限で決まる。
方針：join の零単体は左右のいずれかから来ることを頂点での検出に使う。
規約：両因子は任意の単体集合。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐からの比較の引き戻しの条件の検査。 -/
lemma relativeJoinCone_hom_ext_stdSimplex {A B : SSet.{u}} {n : ℕ}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ (Δ[n] : SSet.{u})}
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ g)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ g) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨l, hl⟩, a, b⟩
  cases l with
  | zero =>
    cases a
    exact congrArg (fun k : B ⟶ (Δ[n] : SSet.{u}) ↦ k.app (Opposite.op ⦋0⦌) b) hB
  | succ l =>
    have he : l = 0 := by change l + 1 < 2 at hl; omega
    subst l
    cases b
    exact congrArg (fun k : A ⟶ (Δ[n] : SSet.{u}) ↦ k.app (Opposite.op ⦋0⦌) a) hA

/-- 概要：標準単体の右錐への左包含は大きい標準単体の最後の面の包含。
方針：標準単体の join の同型を各頂点で計算する。
規約：右の点は標準零単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、終域の小さい面の右錐表示。 -/
lemma relativeJoinCone_stdSimplex_inl (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom =
      stdSimplex.δ (Fin.last (n + 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  fin_cases i
  apply Fin.ext
  change (a 0).val = ((Fin.last (n + 1)).succAbove (a 0)).val
  rw [Fin.succAbove_last]
  rfl

/-- 概要：標準単体の右錐の点は大きい標準単体の最後の頂点に写る。
方針：零単体で join の同型を計算する。
規約：右の点を始域とする定値射の式。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の新しい頂点。 -/
lemma relativeJoinCone_stdSimplex_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro a
  have ha : a = stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have hi := (a i).isLt
    change (a i).val = 0
    omega
  subst a
  apply stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- 概要：区間の右錐から区間への時刻の射。
方針：右錐を標準二単体と同定し、後ろの二頂点を一に合わせる退化を使う。
規約：元の時刻零と一を保ち、新しい右頂点も一へ送る。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の右錐の底の区間成分。 -/
noncomputable def relativeJoinConeTime : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) Δ[0] ⟶ Δ[1] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ (1 : Fin 2)

/-- 概要：右錐の時刻の射は元の区間で恒等射。
方針：区間の二つの頂点で計算する。
規約：区間は右錐の左因子。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の元の因子での時刻。 -/
lemma relativeJoinConeTime_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ relativeJoinConeTime = 𝟙 Δ[1] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  fin_cases i <;> apply stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl

/-- 概要：右錐の新しい頂点の時刻は一。
方針：標準零単体の唯一の頂点で計算する。
規約：一への定値射として等式を与える。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の新しい頂点での時刻。 -/
lemma relativeJoinConeTime_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ relativeJoinConeTime =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro a
  have ha : a = stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have hi := (a i).isLt
    change (a i).val = 0
    omega
  subst a
  apply stdSimplex.ext
  intro i
  fin_cases i
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
