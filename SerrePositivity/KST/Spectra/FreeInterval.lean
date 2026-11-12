module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FreeInterval

public import SerrePositivity.KST.Spectra.PointedIntervalAnodyne
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators

/-!
概要：自由な基点を加えた区間と二つの端点の包含。
方針：零次単体の面の anodyne 性を、基点との余積と単位の同型へ移す。
規約：面添字一が時刻零、面添字零が時刻一。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。任意の射の mapping path 置換。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：anodyne な単体集合の射は単射。
方針：全ての単射への RLP はホーンへの RLP を含み、境界生成の左クラスへ移す。
規約：モデル構造の弱同値の公理は用いない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。自由な端点包含の単射性。 -/
theorem anodyne_mono {A B : SSet.{u}} (i : A ⟶ B) (hi : anodyneExtensions i) : Mono i := by
  have h : I.rlp.llp i := by
    intro E Z p hp
    have hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
      rw [SSet.rlp_monomorphisms]
      exact hp
    exact hi p (fun _ _ j hj ↦ hp' j (J_le_monomorphisms _ hj))
  rw [boundaryGenerators_leftClass] at h
  exact h

/-- 概要：自由な区間の端点包含は単射。
方針：証明済みの anodyne 射の単射性を使う。
規約：基礎単体集合の射について述べる。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7。端点評価の Kan fibration 性。 -/
instance freeIntervalEndpoint_mono (i : Fin 2) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i).right :=
  anodyne_mono _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_anodyne i)

end

end SerrePositivity.KST.Spectra
