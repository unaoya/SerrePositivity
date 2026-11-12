module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationInitialChoice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-! # 始対象による fiber の Hom 表示と零因子分解

概要：全空間の始対象からの射が底の零対象を経由すると、その fiber の Hom 表示は零射になる。
方針：始対象からの射の一意性で因子分解を作り、底へ送って零対象からの射を消す。
規約：充填性を使わない頂点の公式と、left fibration の π₀ の公式を分ける。使われ方：ループ単位の零射との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：始対象からの fiber 頂点への射が底の零対象を経由すれば、その Hom 表示は零射。
方針：始対象からの一意の射を中間頂点と指定射の合成に置き換え、底の零対象を使う。
規約：全空間の quasicategory 性と底の零射構造を仮定。使われ方：余錐の畳み込みの零因子分解。 -/
lemma leftFibrationInitialVertexHom_eq_zero_of_factor {E B : SSet.{u}} [Quasicategory E]
    [HasZeroMorphisms B.HomotopyCategory] (p : E ⟶ B)
    (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e) (y : B _⦋0⦌) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) _⦋0⦌)
    (d : E _⦋0⦌) (b : (SSet.HomotopyCategory.mk d : hoFunctor.obj E) ⟶
      SSet.HomotopyCategory.mk s.val)
    (hd : IsZero (SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) d) : hoFunctor.obj B)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom p e he y s = 0 := by
  let : HasZeroMorphisms (hoFunctor.obj B) :=
    inferInstanceAs (HasZeroMorphisms B.HomotopyCategory)
  have h : he.isInitialHo.to (SSet.HomotopyCategory.mk s.val) =
      he.isInitialHo.to (SSet.HomotopyCategory.mk d) ≫ b := he.isInitialHo.hom_ext _ _
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom]
  rw [h, CategoryTheory.Functor.map_comp]
  have hb : (hoFunctor.map p).toFunctor.map b = 0 := hd.eq_of_src _ _
  rw [hb, comp_zero, zero_comp]

/-- 概要：同じ底上の関手の元に零像を持つ始対象があれば、誘導された fiber の Hom 表示は零射。
方針：元の始対象からの射を関手で送り、底の零対象を通る因子分解の公式を使う。
規約：標的の射は left fibration、元の射に充填性は不要。使われ方：零頂点を持つ辺の余錐の制限。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_map_eq_zero
    {E F B : SSet.{u}} [Quasicategory E] [Quasicategory F] [Quasicategory B]
    [HasZeroMorphisms B.HomotopyCategory]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) (f : F ⟶ E) (hf : f ≫ p = q)
    (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e) (d : F _⦋0⦌) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex d)
    (hz : IsZero (SSet.HomotopyCategory.mk (q.app (Opposite.op ⦋0⦌) d) : hoFunctor.obj B))
    (y : B _⦋0⦌) (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p e he y
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p f hf y) a) = 0 := by
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective a
  rw [SSet.mapπ₀_mk, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_mk]
  let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p f hf y).app (Opposite.op ⦋0⦌) s
  let d' := f.app (Opposite.op ⦋0⦌) d
  have hv : p.app (Opposite.op ⦋0⦌) d' = q.app (Opposite.op ⦋0⦌) d :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf (Opposite.op ⦋0⦌)) d
  have hz' : IsZero (SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) d') : hoFunctor.obj B) :=
    hz.of_iso (eqToIso (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B)) hv))
  let b : (SSet.HomotopyCategory.mk d' : hoFunctor.obj E) ⟶ SSet.HomotopyCategory.mk t.val :=
    (hoFunctor.map f).toFunctor.map (hd.isInitialHo.to (SSet.HomotopyCategory.mk s.val))
  exact leftFibrationInitialVertexHom_eq_zero_of_factor p e he y t d' b hz'

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
