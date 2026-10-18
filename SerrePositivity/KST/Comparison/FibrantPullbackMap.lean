module

public import SerrePositivity.KST.Comparison.KanBasePullback
public import SerrePositivity.KST.Comparison.ReplacementComparison

/-!
# Kan 基底上の二つのファイバー方向の比較

概要：Kan fibration の間の局所化同型は任意の射に沿って引き戻しても可逆となる。
方針：先に引き戻す射が fibration の場合を積の対称性で示し、一般の場合はその射も置換する。
規約：Segal 1974 Proposition 1.6 のホモトピー引き戻し模型の比較。基底の Kan 性を使う。
使われ方：基底を固定して二つの入力を動かす比較の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：基底上の比較を引き戻す写像は、積の対称同型でスライスの積の写像に一致する。
方針：二つの射影を計算する。
規約：比較の第一変数は固定する。
使われ方：左変数が Kan fibration の場合の局所化可逆性。
-/
theorem pullbackMapBase_swap {T₀ T₁ X B : SSet.{u}}
    (p₀ : T₀ ⟶ B) (p₁ : T₁ ⟶ B) (f : X ⟶ B) (k : T₀ ⟶ T₁) (hk : k ≫ p₁ = p₀) :
    pullbackMapBase p₀ p₁ f k hk = (pullbackSymmetry f p₀).hom ≫
      (sliceFiberFunctor f).map (Over.homMk k hk : Over.mk p₀ ⟶ Over.mk p₁) ≫
        (pullbackSymmetry p₁ f).hom := by
  let v : Over.mk p₀ ⟶ Over.mk p₁ := Over.homMk k hk
  let m : pullback p₀ f ⟶ pullback p₁ f := (sliceFiberFunctor f).map v
  have hm₀ : m ≫ pullback.fst p₁ f = pullback.fst p₀ f ≫ k :=
    sliceFiberFunctor_map_fst f v
  have hm₁ : m ≫ pullback.snd p₁ f = pullback.snd p₀ f :=
    sliceFiberFunctor_map_snd f v
  change pullbackMapBase p₀ p₁ f k hk =
    (pullbackSymmetry f p₀).hom ≫ m ≫ (pullbackSymmetry p₁ f).hom
  apply pullback.hom_ext
  · rw [pullbackMapBase_fst, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_fst, hm₁, pullbackSymmetry_hom_comp_snd]
  · rw [pullbackMapBase_snd, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_snd, hm₀, ← Category.assoc, pullbackSymmetry_hom_comp_fst]

/--
概要：Kan 基底上の局所化同型は、Kan fibration で引き戻すと可逆となる。
方針：積の対称性でスライスの積の既証の不変性を適用する。
規約：比較される二つの対象の構造射の Kan 性は不要。
使われ方：任意の左変数を Kan 分解した後の比較。
-/
theorem pullbackMapBase_localized_isIso_of_fibration {T₀ T₁ X B : SSet.{u}}
    [SSet.KanComplex B] (p₀ : T₀ ⟶ B) (p₁ : T₁ ⟶ B)
    (f : X ⟶ B) (hf : SSet.modelCategoryQuillen.J.rlp f)
    (k : T₀ ⟶ T₁) (hk : k ≫ p₁ = p₀)
    (hki : IsIso (AnodyneHomotopy.anodyneQ.map k)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (pullbackMapBase p₀ p₁ f k hk)) := by
  let v : Over.mk p₀ ⟶ Over.mk p₁ := Over.homMk k hk
  have h : IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor f).map v)) :=
    sliceFiberFunctor_localized_isIso f hf v hki
  rw [pullbackMapBase_swap]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/--
概要：Kan 基底上の Kan fibration の間の局所化同型は任意の射で引き戻しても可逆となる。
方針：左射を anodyne–Kan 分解し、二つの積の縦方向の比較と可換な四角形を作る。
規約：Segal 1974 Proposition 1.6 の補助。基底の Kan 性と両方の右射の Kan 性を使う。
使われ方：ホモトピー引き戻し模型の右入力に関する不変性。
-/
theorem pullbackMapBase_localized_isIso_of_kan_base {T₀ T₁ X B : SSet.{u}}
    [SSet.KanComplex B] (p₀ : T₀ ⟶ B) (hp₀ : SSet.modelCategoryQuillen.J.rlp p₀)
    (p₁ : T₁ ⟶ B) (hp₁ : SSet.modelCategoryQuillen.J.rlp p₁)
    (f : X ⟶ B) (k : T₀ ⟶ T₁) (hk : k ≫ p₁ = p₀)
    (hki : IsIso (AnodyneHomotopy.anodyneQ.map k)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (pullbackMapBase p₀ p₁ f k hk)) := by
  let d := AnodyneKanReplacement.factorization.factorizationData f
  let j : Over.mk f ⟶ Over.mk d.p := Over.homMk d.i d.fac
  let a₀ : pullback f p₀ ⟶ pullback d.p p₀ := (sliceFiberFunctor p₀).map j
  let a₁ : pullback f p₁ ⟶ pullback d.p p₁ := (sliceFiberFunctor p₁).map j
  let b₀ := pullbackMapBase p₀ p₁ f k hk
  let b₁ := pullbackMapBase p₀ p₁ d.p k hk
  have ha₀ : IsIso (AnodyneHomotopy.anodyneQ.map a₀) :=
    sliceFiberFunctor_anodyne_localized_isIso p₀ hp₀ j d.hi
  have ha₁ : IsIso (AnodyneHomotopy.anodyneQ.map a₁) :=
    sliceFiberFunctor_anodyne_localized_isIso p₁ hp₁ j d.hi
  have hb₁ : IsIso (AnodyneHomotopy.anodyneQ.map b₁) :=
    pullbackMapBase_localized_isIso_of_fibration p₀ p₁ d.p d.hp k hk hki
  have ha₀fst : a₀ ≫ pullback.fst d.p p₀ = pullback.fst f p₀ ≫ d.i :=
    sliceFiberFunctor_map_fst p₀ j
  have ha₀snd : a₀ ≫ pullback.snd d.p p₀ = pullback.snd f p₀ :=
    sliceFiberFunctor_map_snd p₀ j
  have ha₁fst : a₁ ≫ pullback.fst d.p p₁ = pullback.fst f p₁ ≫ d.i :=
    sliceFiberFunctor_map_fst p₁ j
  have ha₁snd : a₁ ≫ pullback.snd d.p p₁ = pullback.snd f p₁ :=
    sliceFiberFunctor_map_snd p₁ j
  have hcomm : a₀ ≫ b₁ = b₀ ≫ a₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackMapBase_fst, ha₀fst,
        Category.assoc, ha₁fst, ← Category.assoc, pullbackMapBase_fst]
    · rw [Category.assoc, pullbackMapBase_snd, ← Category.assoc,
        ha₀snd, Category.assoc, ha₁snd, pullbackMapBase_snd]
  have h := congrArg AnodyneHomotopy.anodyneQ.map hcomm
  rw [Functor.map_comp, Functor.map_comp] at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map b₀ ≫ AnodyneHomotopy.anodyneQ.map a₁) :=
    h ▸ inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map a₀ ≫
      AnodyneHomotopy.anodyneQ.map b₁))
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Comparison
