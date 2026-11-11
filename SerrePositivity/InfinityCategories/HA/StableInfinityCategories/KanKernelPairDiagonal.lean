module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairNaturality

/-! # 自己引き戻しの対角とループの恒等射

概要：自己引き戻しの対角の連結成分はループ表示で恒等射になる。
方針：基点自身を元の固定 fiber の頂点として取り、始対象の自己射の一意性を使う。
規約：群演算の単位との比較であり、Hom の零射との比較は別に行う。使われ方：演算の加法との同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：任意の射の自己引き戻しに対角写像がある。
方針：二つの恒等射を引き戻しの普遍性で組にする。
規約：充填性は不要。使われ方：ループの単位となる余錐の指定。 -/
def kanKernelPairDiagonal {E B : SSet.{u}} (p : E ⟶ B) : E ⟶ pullback p p :=
  pullback.lift (𝟙 E) (𝟙 E) rfl

/-- 概要：対角の第一成分は恒等射。
方針：持ち上げの第一成分を計算する。
規約：射の等号。使われ方：対角の頂点の固定 fiber による表示。 -/
lemma kanKernelPairDiagonal_fst {E B : SSet.{u}} (p : E ⟶ B) :
    kanKernelPairDiagonal p ≫ pullback.fst p p = 𝟙 E := pullback.lift_fst _ _ _

/-- 概要：対角の第二成分は恒等射。
方針：持ち上げの第二成分を計算する。
規約：射の等号。使われ方：対角の頂点の基点との一致。 -/
lemma kanKernelPairDiagonal_snd {E B : SSet.{u}} (p : E ⟶ B) :
    kanKernelPairDiagonal p ≫ pullback.snd p p = 𝟙 E := pullback.lift_snd _ _ _

/-- 概要：対角は全空間の射から誘導した自己引き戻しの射と可換。
方針：引き戻しの両射影で計算する。
規約：充填性の仮定は不要。使われ方：ループの単位の自然性。 -/
lemma kanKernelPairDiagonal_map {E B E' B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g) :
    kanKernelPairDiagonal p ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap p q f g h = f ≫ kanKernelPairDiagonal q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_fst, kanKernelPairDiagonal_fst]
    rw [← Category.assoc, kanKernelPairDiagonal_fst, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_snd, kanKernelPairDiagonal_snd]
    rw [← Category.assoc, kanKernelPairDiagonal_snd, Category.id_comp, Category.comp_id]

/-- 概要：自己引き戻しの対角は基点からのループ表示で恒等射を表す。
方針：基点自身の固定 fiber の頂点で対角を表し、始対象の自己射が恒等となることを使う。
規約：E と B は Kan、E は可縮、p は Kan fibration。使われ方：ループ演算の単位の計算。 -/
lemma kanKernelPairPiZeroLoopEquiv_diagonal {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e
      (SSet.mapπ₀ (kanKernelPairDiagonal p) (SSet.π₀.mk e)) = 𝟙 _ := by
  let s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (p.app (Opposite.op ⦋0⦌) e)) _⦋0⦌ :=
    ⟨e, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩
  have hs : SSet.yonedaEquiv.symm e ≫ kanKernelPairDiagonal p =
      SSet.yonedaEquiv.symm s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion p e := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, kanKernelPairDiagonal_fst,
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_fst, Category.comp_id, SSet.yonedaEquiv_symm_comp]
      rfl
    · rw [Category.assoc, Category.assoc, kanKernelPairDiagonal_snd,
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_snd, Category.comp_id, SSet.comp_const,
        SSet.yonedaEquiv_symm_zero]
  have hv := congrArg (SSet.yonedaEquiv (X := pullback p p) (n := ⦋0⦌)) hs
  simp only [SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply] at hv
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e (SSet.π₀.mk _) = _
  rw [hv, ← SSet.mapπ₀_mk, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_fiber_mk]
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom]
  have hi : (hE.isInitialVertex e).isInitialHo.to (SSet.HomotopyCategory.mk s.val) =
      𝟙 (SSet.HomotopyCategory.mk e : hoFunctor.obj E) :=
    (hE.isInitialVertex e).isInitialHo.hom_ext _ _
  rw [hi]
  simp only [CategoryTheory.Functor.map_id, eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
