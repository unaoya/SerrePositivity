module

public import SerrePositivity.KST.Comparison.KanAnodyneBaseChange
public import SerrePositivity.KST.Comparison.FibrantTargetLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization

/-!
# Kan 基底上の局所化同型の引き戻し

概要：Kan 基底上の Kan fibration との積が局所化同型を保つことを証明する。
方針：右随伴の Kan 性と、局所化可逆な単射・全単射的右持ち上げ性への分解を使う。
規約：Segal 1974 Proposition 1.6 の貼り合わせの補助。基底の Kan 性を明示する。
使われ方：置換済みの基底上でのホモトピー引き戻しの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

/--
概要：Kan 基底上では基底変換の右随伴は Kan 複体を Kan な全空間に送る。
方針：終射に対する既証の持ち上げ性と右随伴の終対象保存を合成する。
規約：基底 B の Kan 性を使う。
使われ方：局所化可逆な単射の右随伴への持ち上げ。
-/
theorem sliceFiberRightAdjoint_kan {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) [SSet.KanComplex B]
    (K : SSet.{u}) [SSet.KanComplex K] :
    SSet.KanComplex ((sliceFiberFunctor p).rightAdjoint.obj K).left := by
  let G := (sliceFiberFunctor p).rightAdjoint
  have hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  have hq := sliceFiberRightAdjoint_test_rlp p hp (terminal.from K)
    (KanTestLiftingClass.RightTests.terminal K hK)
  have hT : IsTerminal (G.obj (⊤_ SSet.{u})) := IsTerminal.isTerminalObj G _ terminalIsTerminal
  let e := hT.uniqueUpToIso (Over.mkIdTerminal (X := B))
  have he : e.hom.left = (G.obj (⊤_ SSet.{u})).hom := by
    have h := Over.w e.hom
    change e.hom.left ≫ (𝟙 B) = (G.obj (⊤_ SSet.{u})).hom at h
    exact (Category.comp_id (show (G.obj (⊤_ SSet.{u})).left ⟶ B from e.hom.left)).symm.trans h
  let : IsIso (G.obj (⊤_ SSet.{u})).hom := by
    rw [← he]
    exact inferInstanceAs (IsIso ((Over.forget B).map e.hom))
  let : SSet.KanComplex (G.obj (⊤_ SSet.{u})).left :=
    isFibrant_of_fibration (G.obj (⊤_ SSet.{u})).hom
  let : Fibration (G.map (terminal.from K)).left :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr hq
  exact isFibrant_of_fibration (G.map (terminal.from K)).left

/--
概要：Kan 基底上の積は局所化可逆な単射を局所化同型に送る。
方針：検出用の右テストの終域を右随伴で Kan に保ち、随伴で左持ち上げ性を移す。
規約：Segal 1974 Proposition 1.6 の貼り合わせの補助。単射性と Kan 基底を使う。
使われ方：一般の局所化同型の引き戻しへ単射分解で進む。
-/
theorem sliceFiberFunctor_localizedMono_isIso {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) [SSet.KanComplex B]
    {X Y : Over B} (i : X ⟶ Y) [Mono i.left]
    (hi : IsIso (AnodyneHomotopy.anodyneQ.map i.left)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor p).map i)) := by
  let F := sliceFiberFunctor p
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  apply KanTestLiftingClass.localized_isIso_of_llp
  intro K L q hq
  have hGq := sliceFiberRightAdjoint_test_rlp p hp q hq
  have hL : SSet.KanComplex L := by
    cases hq with
    | terminal K hK =>
      change Fibration (terminal.from (⊤_ SSet.{u}))
      have : IsIso (terminal.from (⊤_ SSet.{u})) :=
        isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
      infer_instance
    | paths K hK =>
      let : Fibration (terminal.from K) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
      let : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
      exact inferInstanceAs (SSet.KanComplex ((ihom (SSet.boundary.{u} 1).toSSet).obj K))
  let : SSet.KanComplex (G.obj L).left := sliceFiberRightAdjoint_kan p hp L
  exact (adj.hasLiftingProperty_iff i q).mpr
    (over_lifting_of_underlying i (G.map q)
      (localizedMono_lifting_fibrantTarget i.left hi _ hGq))

/--
概要：Kan 基底上の積は任意の局所化同型を保つ。
方針：射を局所化可逆な単射と全単射的右持ち上げ性を持つ射に分解する。
規約：Segal 1974 Proposition 1.6 の補助。基底は Kan とする。
使われ方：置換済みの基底上の引き戻し比較。
-/
theorem sliceFiberFunctor_localized_isIso {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) [SSet.KanComplex B]
    {X Y : Over B} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.left)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor p).map f)) := by
  let F := sliceFiberFunctor p
  let l := MonoLocalizedFactorization.left f.left
  let r := MonoLocalizedFactorization.right f.left
  let Z : Over B := Over.mk (r ≫ Y.hom)
  let j : X ⟶ Z := Over.homMk l (by
    change l ≫ (r ≫ Y.hom) = X.hom
    rw [← Category.assoc, MonoLocalizedFactorization.fac, Over.w f])
  let k : Z ⟶ Y := Over.homMk r
  have hjk : j ≫ k = f := by
    apply Over.OverMorphism.ext
    exact MonoLocalizedFactorization.fac f.left
  have : Mono j.left := inferInstanceAs (Mono (MonoLocalizedFactorization.left f.left))
  have hl : IsIso (AnodyneHomotopy.anodyneQ.map j.left) :=
    (MonoLocalizedFactorization.left_localized_isIso_iff f.left).mpr hf
  have hj : IsIso (AnodyneHomotopy.anodyneQ.map (F.map j)) :=
    sliceFiberFunctor_localizedMono_isIso p hp j hl
  have hr : (MorphismProperty.monomorphisms SSet.{u}).rlp k.left :=
    MonoLocalizedFactorization.right_all_mono_rlp f.left
  have hrF : (MorphismProperty.monomorphisms SSet.{u}).rlp (F.map k) :=
    (MorphismProperty.monomorphisms SSet.{u}).rlp.of_isPullback
      (sliceFiberFunctor_map_isPullback p k).flip hr
  have hk : IsIso (AnodyneHomotopy.anodyneQ.map (F.map k)) :=
    MonoRightLiftingContraction.localized_isIso _ hrF
  rw [← hjk, F.map_comp, Functor.map_comp]
  infer_instance

/--
概要：Kan 基底上の Kan fibration に沿う局所化同型の引き戻しは局所化同型である。
方針：終対象へ向かうスライスの射を積で移し、任意の引き戻しの同型へ運ぶ。
規約：Segal 1974 Proposition 1.6 の補助。任意の非 Kan 基底については主張しない。
使われ方：Kan 置換済みの図式の貼り合わせ。
-/
theorem pullback_localized_isIso_of_kan_base {A B E P : SSet.{u}} [SSet.KanComplex B]
    (i : A ⟶ B) (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
    (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (j : P ⟶ E) (k : P ⟶ A) (sq : IsPullback j k p i) :
    IsIso (AnodyneHomotopy.anodyneQ.map j) := by
  let f : Over.mk i ⟶ Over.mk (𝟙 B) := Over.homMk i
  have hf : IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor p).map f)) :=
    sliceFiberFunctor_localized_isIso p hp f hi
  have hs : (sliceFiberFunctor p).map f ≫ pullback.snd (𝟙 B) p = pullback.snd i p :=
    sliceFiberFunctor_map_snd p f
  have ht : IsIso (AnodyneHomotopy.anodyneQ.map (pullback.snd i p)) := by
    rw [← hs, Functor.map_comp]
    infer_instance
  let e := sq.isoIsPullback _ _ (IsPullback.of_hasPullback i p).flip
  have he : e.hom ≫ pullback.snd i p = j := sq.isoIsPullback_hom_fst ..
  rw [← he, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
