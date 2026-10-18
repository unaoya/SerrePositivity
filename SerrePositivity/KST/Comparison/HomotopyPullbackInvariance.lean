module

public import SerrePositivity.KST.Comparison.FibrantPullbackMap

/-!
# Kan 基底を固定したホモトピー引き戻しの不変性

概要：基底が Kan のとき、二つの入力の局所化同型はホモトピー引き戻し模型の同型を誘導する。
方針：右入力の Kan 分解の比較と、左入力を動かす積の比較に分ける。
規約：Segal 1974 Proposition 1.6 の貼り合わせの補助。固定模型の実際の比較射を使う。
使われ方：骨格の各部で行う置換の整合。
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
概要：ホモトピー引き戻しの比較射の第一射影。
方針：引き戻しへの持ち上げの計算則を使う。
規約：左入力への射 a を後合成する。
使われ方：比較写像の因子化と自然性。
-/
@[reassoc] theorem homotopyPullbackMap_fst {X Y Z X' Y' Z' : SSet.{u}}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z')
    (hf : f ≫ c = a ≫ f') (hg : g ≫ c = b ≫ g') :
    homotopyPullbackMap a b c hf hg ≫ pullback.fst f'
      (AnodyneKanReplacement.factorization.p.app (Arrow.mk g')) =
        pullback.fst f (AnodyneKanReplacement.factorization.p.app (Arrow.mk g)) ≫ a :=
  pullback.lift_fst ..

/--
概要：ホモトピー引き戻しの比較射の第二射影。
方針：右入力の関手的な分解の写像を計算する。
規約：右入力の arrow の比較は b と c から作る。
使われ方：分解の自然性との照合。
-/
@[reassoc] theorem homotopyPullbackMap_snd {X Y Z X' Y' Z' : SSet.{u}}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z')
    (hf : f ≫ c = a ≫ f') (hg : g ≫ c = b ≫ g') :
    homotopyPullbackMap a b c hf hg ≫ pullback.snd f'
      (AnodyneKanReplacement.factorization.p.app (Arrow.mk g')) =
        pullback.snd f (AnodyneKanReplacement.factorization.p.app (Arrow.mk g)) ≫
          AnodyneKanReplacement.factorization.Z.map
            (show Arrow.mk g ⟶ Arrow.mk g' from Arrow.homMk b c hg.symm) :=
  pullback.lift_snd ..

/--
概要：Kan 基底を固定した二つの入力の局所化同型はホモトピー引き戻し模型の同型を誘導する。
方針：右入力の分解の比較を引き戻し、次に左入力の比較を積で送る。
規約：Segal 1974 Proposition 1.6 の補助。基底の Kan 性を明示する。
使われ方：置換した骨格の各部分のホモトピー引き戻し比較。
-/
theorem homotopyPullbackMap_localized_isIso_fixed_kan_base {X Y X' Y' B : SSet.{u}}
    [SSet.KanComplex B] {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B} {g' : Y' ⟶ B}
    (a : X ⟶ X') (b : Y ⟶ Y') (hf : f ≫ 𝟙 B = a ≫ f') (hg : g ≫ 𝟙 B = b ≫ g')
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hb : IsIso (AnodyneHomotopy.anodyneQ.map b)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackMap a b (𝟙 B) hf hg)) := by
  let d₀ := AnodyneKanReplacement.factorization.factorizationData g
  let d₁ := AnodyneKanReplacement.factorization.factorizationData g'
  let φ : Arrow.mk g ⟶ Arrow.mk g' := Arrow.homMk b (𝟙 B) hg.symm
  let z : d₀.Z ⟶ d₁.Z := AnodyneKanReplacement.factorization.Z.map φ
  have hz : z ≫ d₁.p = d₀.p := by
    have h := AnodyneKanReplacement.factorization.p.naturality φ
    change z ≫ d₁.p = d₀.p ≫ 𝟙 B at h
    exact h.trans (Category.comp_id _)
  have hi : d₀.i ≫ z = b ≫ d₁.i :=
    (AnodyneKanReplacement.factorization.i.naturality φ).symm
  have hi₀ : IsIso (AnodyneHomotopy.anodyneQ.map d₀.i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions d₀.i d₀.hi
  have hi₁ : IsIso (AnodyneHomotopy.anodyneQ.map d₁.i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions d₁.i d₁.hi
  have hzi : IsIso (AnodyneHomotopy.anodyneQ.map z) := by
    have hcomp : IsIso (AnodyneHomotopy.anodyneQ.map d₀.i ≫
        AnodyneHomotopy.anodyneQ.map z) := by
      rw [← Functor.map_comp, hi, Functor.map_comp]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hcomp
  let r := pullbackMapBase d₀.p d₁.p f z hz
  let av : Over.mk f ⟶ Over.mk f' := Over.homMk a (by
    exact hf.symm.trans (Category.comp_id _))
  let s : pullback f d₁.p ⟶ pullback f' d₁.p := (sliceFiberFunctor d₁.p).map av
  have hr : IsIso (AnodyneHomotopy.anodyneQ.map r) :=
    pullbackMapBase_localized_isIso_of_kan_base d₀.p d₀.hp d₁.p d₁.hp f z hz hzi
  have hs : IsIso (AnodyneHomotopy.anodyneQ.map s) :=
    sliceFiberFunctor_localized_isIso d₁.p d₁.hp av ha
  have hsf : s ≫ pullback.fst f' d₁.p = pullback.fst f d₁.p ≫ a :=
    sliceFiberFunctor_map_fst d₁.p av
  have hss : s ≫ pullback.snd f' d₁.p = pullback.snd f d₁.p :=
    sliceFiberFunctor_map_snd d₁.p av
  let m : pullback f d₀.p ⟶ pullback f' d₁.p := homotopyPullbackMap a b (𝟙 B) hf hg
  have hmf : m ≫ pullback.fst f' d₁.p = pullback.fst f d₀.p ≫ a :=
    homotopyPullbackMap_fst a b (𝟙 B) hf hg
  have hms : m ≫ pullback.snd f' d₁.p = pullback.snd f d₀.p ≫ z :=
    homotopyPullbackMap_snd a b (𝟙 B) hf hg
  have hfac : m = r ≫ s := by
    apply pullback.hom_ext
    · rw [hmf, Category.assoc, hsf, ← Category.assoc, pullbackMapBase_fst]
    · rw [hms, Category.assoc, hss, pullbackMapBase_snd]
  change IsIso (AnodyneHomotopy.anodyneQ.map m)
  rw [hfac, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
