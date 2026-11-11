module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairFiber

/-! # 可換正方形による自己引き戻しと固定 fiber の写像

概要：fibration 間の可換正方形は自己引き戻しと指定基点の固定 fiber に写像を誘導する。
方針：引き戻しと頂点 fiber の普遍性を使い、包含後に可換性を確認する。
規約：この段階では充填性を仮定しない。使われ方：ループ比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：可換正方形は二つの自己引き戻しの間の射を誘導する。
方針：元の両射影に全空間の射を合成して引き戻しに持ち上げる。
規約：可換性は f ≫ q = p ≫ g の向き。使われ方：余錐空間の後合成によるループの写像。 -/
def kanKernelPairMap {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) : pullback p p ⟶ pullback q q :=
  pullback.lift (pullback.fst p p ≫ f) (pullback.snd p p ≫ f) (by
    simp only [Category.assoc, h]
    rw [← Category.assoc, pullback.condition, Category.assoc])

/-- 概要：誘導された自己引き戻しの射の第一成分は元の第一成分の像。
方針：引き戻しの持ち上げの第一成分を計算する。
規約：射の等号。使われ方：固定 fiber の包含との可換性。 -/
lemma kanKernelPairMap_fst {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) :
    kanKernelPairMap p q f g h ≫ pullback.fst q q = pullback.fst p p ≫ f :=
  pullback.lift_fst _ _ _

/-- 概要：誘導された自己引き戻しの射の第二成分は元の第二成分の像。
方針：引き戻しの持ち上げの第二成分を計算する。
規約：射の等号。使われ方：基点の像を固定する計算。 -/
lemma kanKernelPairMap_snd {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) :
    kanKernelPairMap p q f g h ≫ pullback.snd q q = pullback.snd p p ≫ f :=
  pullback.lift_snd _ _ _

/-- 概要：底と全空間の可換正方形を基点で評価すると両側の基点の像は等しい。
方針：可換性を零次成分で評価する。
規約：底の射を先に適用した側からの等号。使われ方：ホモトピー圏の基点輸送。 -/
lemma kanKernelPairMap_basepoint {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) (e : E _⦋0⦌) :
    g.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) e) =
      q.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) e) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌)) e).symm

/-- 概要：可換正方形は基点の像の上の fiber を像の基点の fiber に送る。
方針：元の包含と全空間の射を合成し、底の基点の等号で定値条件を揃える。
規約：像側の基点は f(e)。使われ方：ループ自然性を固定 fiber で計算する。 -/
def kanKernelPairFiberMap {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (p.app (Opposite.op ⦋0⦌) e) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q (q.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) e)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _ ≫ f) (by
    rw [Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp,
      kanKernelPairMap_basepoint p q f g h e])

/-- 概要：誘導された固定 fiber の射は包含後に全空間の射と一致する。
方針：fiber への持ち上げの式を使う。
規約：基点の等号の証明には依存しない。使われ方：代表頂点の像の計算。 -/
lemma kanKernelPairFiberMap_ι {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) (e : E _⦋0⦌) :
    kanKernelPairFiberMap p q f g h e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _ ≫ f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 概要：自己引き戻しの誘導射は基点の固定 fiber の包含と可換。
方針：両射影で、包含と fiber の誘導射の式を計算する。
規約：充填性の仮定は不要。使われ方：ループ比較の自然性の固定 fiber への帰着。 -/
lemma kanKernelPairFiberMap_inclusion {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion p e ≫ kanKernelPairMap p q f g h =
      kanKernelPairFiberMap p q f g h e ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion q (f.app (Opposite.op ⦋0⦌) e) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, kanKernelPairMap_fst, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_fst]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_fst, kanKernelPairFiberMap_ι]
  · simp only [Category.assoc, kanKernelPairMap_snd, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_snd]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_snd, SSet.const_comp, SSet.comp_const]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
