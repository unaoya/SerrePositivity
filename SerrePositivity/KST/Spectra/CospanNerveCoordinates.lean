module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：WalkingCospan の三頂点を標準二単体の頂点 0・1・2 で厳密に表示する。
方針：両始点を 0・1、共通終点を 2 とし、存在する射の条件を全ての場合で計算する。
規約：対象と射を AsSmall で同じ宇宙へ持ち上げる。使われ方：cospan の nerve と Λ[2,2] の同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.CospanShape
noncomputable section

/-- 小さい cospan の頂点を標準二単体の三頂点で表示する。 -/
def cospanVertexIndex (a : AsSmall.{u} WalkingCospan) : Fin 3 :=
  match AsSmall.down.obj a with
  | none => 2
  | some WalkingPair.left => 0
  | some WalkingPair.right => 1

/-- 三頂点の番号から元の小さい cospan の頂点へ戻す。 -/
def cospanIndexVertex (i : Fin 3) : AsSmall.{u} WalkingCospan :=
  if i = 0 then AsSmall.up.obj WalkingCospan.left else
    if i = 1 then AsSmall.up.obj WalkingCospan.right else AsSmall.up.obj WalkingCospan.one

/-- 三頂点の番号表示を戻してから読むと元の番号になる。 -/
lemma cospanVertexIndex_indexVertex (i : Fin 3) :
    cospanVertexIndex (cospanIndexVertex.{u} i) = i := by
  fin_cases i <;> simp [cospanVertexIndex, cospanIndexVertex]

/-- 小さい cospan の頂点を番号で読み直しても元の頂点を保つ。 -/
lemma cospanIndexVertex_vertexIndex (a : AsSmall.{u} WalkingCospan) :
    cospanIndexVertex (cospanVertexIndex a) = a := by
  rcases a with ⟨a⟩
  cases a with
  | none => simp [cospanVertexIndex, cospanIndexVertex]; rfl
  | some k => cases k <;> simp [cospanVertexIndex, cospanIndexVertex] <;> rfl

/-- cospan の射は頂点の番号の順序を保ち、左始点から右始点への射は存在しない。 -/
lemma cospanVertexIndex_hom_condition {a b : AsSmall.{u} WalkingCospan} (f : a ⟶ b) :
    cospanVertexIndex a ≤ cospanVertexIndex b ∧
      ¬ (cospanVertexIndex a = 0 ∧ cospanVertexIndex b = 1) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases f with ⟨f⟩
  change WidePullbackShape.Hom a b at f
  cases f with
  | id a =>
    constructor
    · exact le_rfl
    · omega
  | term k => cases k <;> simp [cospanVertexIndex]

/-- 番号が順序を保ち、二始点を同時に含まないとき、元の cospan に対応する射が存在する。 -/
lemma cospanIndexVertex_nonempty_hom (a b : Fin 3) (hab : a ≤ b)
    (h : ¬ (a = 0 ∧ b = 1)) : Nonempty (cospanIndexVertex.{u} a ⟶ cospanIndexVertex b) := by
  fin_cases a <;> fin_cases b
  all_goals try norm_num at hab
  all_goals try norm_num at h
  all_goals first
    | exact ⟨𝟙 _⟩
    | exact ⟨AsSmall.up.map WalkingCospan.Hom.inl⟩
    | exact ⟨AsSmall.up.map WalkingCospan.Hom.inr⟩

end
end SerrePositivity.KST.Spectra.CospanShape
