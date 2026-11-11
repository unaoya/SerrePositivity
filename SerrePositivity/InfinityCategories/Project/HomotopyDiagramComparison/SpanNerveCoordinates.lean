module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：WalkingSpan の三頂点を標準二単体の頂点 0・1・2 で厳密に表示する。
方針：共通始点を 0、両終点を 1・2 とし、存在する射の条件を全ての場合で計算する。
規約：対象と射を AsSmall で同じ宇宙へ持ち上げる。使われ方：span の nerve と Λ[2,0] の同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 小さい span の頂点を標準二単体の三頂点で表示する。 -/
def spanVertexIndex (a : AsSmall.{u} WalkingSpan) : Fin 3 :=
  match AsSmall.down.obj a with
  | none => 0
  | some WalkingPair.left => 1
  | some WalkingPair.right => 2

/-- 三頂点の番号から元の小さい span の頂点へ戻す。 -/
def spanIndexVertex (i : Fin 3) : AsSmall.{u} WalkingSpan :=
  if i = 0 then AsSmall.up.obj WalkingSpan.zero else
    if i = 1 then AsSmall.up.obj WalkingSpan.left else AsSmall.up.obj WalkingSpan.right

/-- 三頂点の番号表示を戻してから読むと元の番号になる。 -/
lemma spanVertexIndex_indexVertex (i : Fin 3) : spanVertexIndex (spanIndexVertex.{u} i) = i := by
  fin_cases i <;> simp [spanVertexIndex, spanIndexVertex]

/-- 小さい span の頂点を番号で読み直しても元の頂点を保つ。 -/
lemma spanIndexVertex_vertexIndex (a : AsSmall.{u} WalkingSpan) :
    spanIndexVertex (spanVertexIndex a) = a := by
  rcases a with ⟨a⟩
  cases a with
  | none => simp [spanVertexIndex, spanIndexVertex]; rfl
  | some k => cases k <;> simp [spanVertexIndex, spanIndexVertex] <;> rfl

/-- span の射は頂点の番号の順序を保ち、左終点から右終点への射は存在しない。 -/
lemma spanVertexIndex_hom_condition {a b : AsSmall.{u} WalkingSpan} (f : a ⟶ b) :
    spanVertexIndex a ≤ spanVertexIndex b ∧
      ¬ (spanVertexIndex a = 1 ∧ spanVertexIndex b = 2) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases f with ⟨f⟩
  change WidePushoutShape.Hom a b at f
  cases f with
  | id a =>
    constructor
    · exact le_rfl
    · omega
  | init k => cases k <;> simp [spanVertexIndex]

/-- 番号が順序を保ち、二終点を同時に含まないとき、元の span に対応する射が存在する。 -/
lemma spanIndexVertex_nonempty_hom (a b : Fin 3) (hab : a ≤ b)
    (h : ¬ (a = 1 ∧ b = 2)) : Nonempty (spanIndexVertex.{u} a ⟶ spanIndexVertex b) := by
  fin_cases a <;> fin_cases b
  all_goals try norm_num at hab
  all_goals try norm_num at h
  all_goals first
    | exact ⟨𝟙 _⟩
    | exact ⟨AsSmall.up.map WalkingSpan.Hom.fst⟩
    | exact ⟨AsSmall.up.map WalkingSpan.Hom.snd⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
