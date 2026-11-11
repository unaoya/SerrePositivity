module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedBoundaryLifting

/-!
概要：係数図式の成分ごとの自明 Kan fibration は weighted nerve でも自明 Kan fibration。
方針：最後の係数の相対境界を充填し、最後の面と合わせて全体の境界を復元する。
規約：底の小圏と係数図式の Kan 性は要求しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の homotopy 極限の係数に関する不変性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {C : Type u} [Category.{u} C]

/-- 概要：底の全標準単体上の係数評価は図式の最後の成分そのもの。
方針：恒等単調写像での係数の明示式を使い、恒等射の輸送を除く。
規約：可換条件の証明は任意に指定できる。
使われ方：Kerodon 5.3.3.1（Tag 025X） の比較先の相対境界の最後の値。 -/
lemma weightedCoefficient_yoneda (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C n) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ F)
    (h : SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm σ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ
        (SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n)) (𝟙 _) h =
      θ.app (Fin.last n) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_diagram F σ (𝟙 ⦋n⦌) θ
    (show SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = stdSimplex.map (𝟙 ⦋n⦌) ≫ SSet.yonedaEquiv.symm σ by
        simpa only [CategoryTheory.Functor.map_id] using h)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ
      (SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n)) (𝟙 _) h =
    θ.app (Fin.last n) ≫ F.map (σ.map (𝟙 (Fin.last n))) at he
  rw [σ.map_id, F.map_id] at he
  exact he.trans (Category.comp_id (θ.app (Fin.last n)))

/-- 概要：weighted nerve の可換四角形を最後の係数で評価しても可換である。
方針：係数の後合成の自然性とパラメータ自然性を組み合わせ、全単体の係数を計算する。
規約：始域 T と標準単体への射 r は任意。
使われ方：Kerodon 5.3.3.1（Tag 025X） の比較射の境界充填を最後の係数へ還元する。 -/
lemma weightedCoefficient_square {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {n : ℕ}
    (σ : ComposableArrows C n) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ G) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (r : T ⟶ (Δ[n] : SSet.{u}))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = r ≫ SSet.yonedaEquiv.symm σ)
    (sq : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η =
      r ≫ SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a r ha ≫ η.app (σ.obj (Fin.last n)) =
      r ≫ θ.app (Fin.last n) := by
  let b : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G :=
    SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G n)
  have hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G =
      (𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm σ := by
    rw [SSet.yonedaEquiv_symm_comp, Category.id_comp]
    rfl
  have hpost : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G =
      r ≫ SSet.yonedaEquiv.symm σ := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection]
    exact ha
  have hr : (r ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G =
      (r ≫ 𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm σ := by
    rw [Category.assoc, hb, Category.assoc]
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient G σ (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) r hpost :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_postcomp η σ a r ha hpost).symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient G σ (r ≫ b) (r ≫ 𝟙 _) hr :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_congr G σ _ _ _ _ hpost hr sq
        (Category.comp_id r).symm
    _ = r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient G σ b (𝟙 _) hb :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_precomp G σ b (𝟙 _) hb r hr
    _ = _ := by rw [weightedCoefficient_yoneda]

/-- 概要：最後の係数の自明 Kan fibration から正次元の weighted nerve の相対境界を充填できる。
方針：最後の係数で境界を持ち上げて復元し、比較先との一致は最後の面と最後の成分で示す。
規約：指定した底の射列の最後の値の自明 Kan fibration 性だけを使う。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の weighted nerve の比較射の境界充填。 -/
lemma exists_weightedNerveMap_boundary_lift {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ G)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app (σ.obj (Fin.last (n + 1))))]
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (sq : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η = (boundary (n + 1)).ι ≫
      SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G (n + 1))) :
    ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      (boundary (n + 1)).ι ≫ l = a ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η =
        SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G (n + 1)) := by
  let b : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G := SSet.yonedaEquiv.symm ⟨σ, θ⟩
  have hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G = SSet.yonedaEquiv.symm σ := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection η, ← Category.assoc, sq, Category.assoc]
    exact congrArg (fun q ↦ (boundary (n + 1)).ι ≫ q) hb
  have : HasLiftingProperty (boundary (n + 1)).ι
      (η.app (σ.obj (Fin.last (n + 1)))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := η.app (σ.obj (Fin.last (n + 1)))) _ inferInstance
  let csq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha)
      (boundary (n + 1)).ι (η.app (σ.obj (Fin.last (n + 1))))
      (θ.app (Fin.last (n + 1))) := ⟨weightedCoefficient_square η σ θ a _ ha sq⟩
  obtain ⟨ψ, hψ, hlast⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_weightedBoundary_filler_of_last F σ a ha csq.lift csq.fac_left
  let l : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F := SSet.yonedaEquiv.symm ⟨σ, ψ⟩
  let χ := ψ ≫ Functor.whiskerLeft σ η
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G (n + 1) := ⟨σ, χ⟩
  have hs : SSet.yonedaEquiv.symm s = l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  have hboundary : (boundary (n + 1)).ι ≫ (l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) =
      (boundary (n + 1)).ι ≫ b := by
    rw [← Category.assoc, hψ]
    exact sq
  have hχ : χ = θ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedDiagram_eq_of_lastFace G σ
    · apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G) (n := ⦋n⦌)).symm.injective
      change SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)).op s) =
        SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)).op
            (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G (n + 1)))
      rw [← SSet.yonedaEquiv_symm_naturality_left,
        ← SSet.yonedaEquiv_symm_naturality_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
      change stdSimplex.δ (Fin.last (n + 1)) ≫ SSet.yonedaEquiv.symm s =
        stdSimplex.δ (Fin.last (n + 1)) ≫ b
      rw [hs, ← boundary.ι_ι (Fin.last (n + 1)), Category.assoc, hboundary, Category.assoc]
    · change ψ.app (Fin.last (n + 1)) ≫ η.app (σ.obj (Fin.last (n + 1))) = _
      rw [hlast]
      exact csq.fac_right
  refine ⟨l, hψ, ?_⟩
  rw [← hs]
  exact congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ G ↦
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G) (n := ⦋n + 1⦌)).symm ⟨σ, q⟩) hχ

/-- 概要：係数の自明 Kan fibration は weighted nerve の任意の頂点を持ち上げる。
方針：零次元の唯一の係数を、係数の自明 Kan fibration の切断で持ち上げる。
規約：指定した底の頂点を保つ。
使われ方：Kerodon 5.3.3.1（Tag 025X） の零次元の境界充填。 -/
lemma exists_weightedNerveMap_zero_lift {F G : C ⥤ SSet.{u}} (η : F ⟶ G)
    (σ : ComposableArrows C 0) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight 0 ⟶ σ ⋙ G)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app (σ.obj 0))] :
    ∃ l : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η =
        SSet.yonedaEquiv.symm (⟨σ, θ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G 0) := by
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (η.app (σ.obj 0))
  let H : (Δ[0] : SSet.{u}) ⟶ F.obj (σ.obj 0) := θ.app 0 ≫ s
  let ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight 0 ⟶ σ ⋙ F :=
    { app := Fin.cases H (fun i ↦ Fin.elim0 i)
      naturality := by
        intro k l f
        fin_cases k
        fin_cases l
        have hf : f = 𝟙 (0 : Fin 1) := Subsingleton.elim _ _
        subst f
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight 0).map (𝟙 (0 : Fin 1)) ≫ H =
          H ≫ (σ ⋙ F).map (𝟙 (0 : Fin 1))
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
        exact (Category.id_comp H).trans (Category.comp_id H).symm }
  have hψ : ψ ≫ Functor.whiskerLeft σ η = θ := by
    apply NatTrans.ext
    funext k
    fin_cases k
    change (θ.app 0 ≫ s) ≫ η.app (σ.obj 0) = θ.app 0
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q ↦ θ.app 0 ≫ q) hs).trans (Category.comp_id (θ.app 0)))
  refine ⟨SSet.yonedaEquiv.symm (⟨σ, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F 0), ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  change (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G) (n := ⦋0⦌)).symm
    ⟨σ, ψ ≫ Functor.whiskerLeft σ η⟩ = _
  rw [hψ]

/-- 概要：成分ごとの自明 Kan fibration は weighted nerve の全空間でも自明 Kan fibration。
方針：正次元は最後の係数の相対境界から復元し、零次元は係数の切断で持ち上げる。
規約：係数の Kan 性や底の圏の薄さは要求しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の weighted nerve と切断模型の係数比較。 -/
instance weightedNerveMap_trivialKanFibration {F G : C ⥤ SSet.{u}} (η : F ⟶ G)
    [∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app c)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨⟨σ, θ⟩, rfl⟩ :=
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G) (n := ⦋n⦌)).symm.surjective b
  cases n with
  | zero =>
    obtain ⟨l, hl⟩ := exists_weightedNerveMap_zero_lift η σ θ
    exact CommSq.HasLift.mk' { l := l, fac_left := boundary.hom_ext₀, fac_right := hl }
  | succ n =>
    obtain ⟨l, hleft, hright⟩ := exists_weightedNerveMap_boundary_lift η σ θ a sq.w
    exact CommSq.HasLift.mk' { l := l, fac_left := hleft, fac_right := hright }

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
