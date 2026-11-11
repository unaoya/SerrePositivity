module
public import SerrePositivity.KST.SConstruction.CoherentSimplexArrows

/-! # Coherent 単体の長辺と合成を結ぶ写像空間の指定辺
概要：長辺の通常の射から二辺の通常の合成への、豊穣 Hom 内の実際の辺を復号する。
方針：端点だけの Path を二つの Path の和へ含め、元の豊穣作用を評価する。
規約：局所 Kan 性や新しいホモトピー代表の選択は不要。
使われ方：元の自然性 square の二つの三角形から実適合ホモトピーを作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 二つの端点 Path の元の thickening での合成。 -/
def coherentEndpointPathComposite {J : Type u} [LinearOrder J] {a b c : J}
    (hab : a ≤ b) (hbc : b ≤ c) : Path a c where
  I := (coherentEndpointPath hab).I ∪ (coherentEndpointPath hbc).I
  left := Or.inl (Or.inl rfl)
  right := Or.inr (Or.inr rfl)
  left_le x hx := by
    rcases hx with hx | hx
    · exact (coherentEndpointPath hab).left_le x hx
    · exact hab.trans ((coherentEndpointPath hbc).left_le x hx)
  le_right x hx := by
    rcases hx with hx | hx
    · exact ((coherentEndpointPath hab).le_right x hx).trans hbc
    · exact (coherentEndpointPath hbc).le_right x hx

/-- 長い端点 Path から合成した Path への元の包含射。 -/
def coherentEndpointPathToComposite {J : Type u} [LinearOrder J] {a b c : J}
    (hab : a ≤ b) (hbc : b ≤ c) :
    coherentEndpointPath (hab.trans hbc) ⟶ coherentEndpointPathComposite hab hbc := by
  refine ⟨⟨⟨?_⟩⟩⟩
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · exact Or.inr (Or.inr hx)

/-- 指定した元の単体から復号した、長辺から二辺の合成への実際の豊穣 Hom の辺。 -/
def coherentSimplexCompositionEdge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (s : (SimplicialNerve C) _⦋n⦌) (i j k : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    (SimplicialCategory.sHom (s.obj (.mk (ULift.up i))) (s.obj (.mk (ULift.up k)))).Edge
      (SimplicialCategory.homEquiv' _ _ (coherentSimplexArrow s i k (hij.trans hjk)))
      (SimplicialCategory.homEquiv' _ _
        (coherentSimplexArrow s i j hij ≫ coherentSimplexArrow s j k hjk)) := by
  let a := (SimplicialThickening.mk (ULift.up i) : SimplicialThickening (ULift.{u} _))
  let b := (SimplicialThickening.mk (ULift.up j) : SimplicialThickening (ULift.{u} _))
  let c := (SimplicialThickening.mk (ULift.up k) : SimplicialThickening (ULift.{u} _))
  let hab : a.as ≤ b.as := hij
  let hbc : b.as ≤ c.as := hjk
  let e := (nerve.edgeMk (coherentEndpointPathToComposite hab hbc)).map (s.map a c)
  refine e.ofEq ?_ ?_
  · simp only [coherentSimplexArrow, Equiv.apply_symm_apply]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp]
    simp only [coherentSimplexArrow, Equiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (s.map_comp a b c) (Opposite.op ⦋0⦌))
      (show ((a ⟶[SSet] b) ⊗ (b ⟶[SSet] c)).obj (Opposite.op ⦋0⦌) from
        (ComposableArrows.mk₀ (coherentEndpointPath hab),
          ComposableArrows.mk₀ (coherentEndpointPath hbc)))

end SerrePositivity.KST.SConstruction
