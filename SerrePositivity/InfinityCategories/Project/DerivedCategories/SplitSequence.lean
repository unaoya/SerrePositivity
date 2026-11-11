module
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # 次数ごとに分裂する列の直和座標

概要：逐次分裂拡大の余極限を初期加群と各商の直和として表示する。
方針：有限段の座標を帰納的に作り、余極限の普遍性で延長する。
規約：分裂は線形写像の分裂だけを要求する。使われ方：semifree filtration の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits
open scoped DirectSum

/-- 概要：初期加群から分裂拡大を繰り返す列のデータ。
方針：包含・商・戻し・切断と五つの分裂等式を保持する。
規約：すべて同じ可換環上の加群。使われ方：filtration を次数ごとに読む。 -/
structure SplitModuleSequence (S : Type u) [CommRing S] where
  stage : ℕ → ModuleCat.{u} S
  quotient : ℕ → ModuleCat.{u} S
  inclusion : ∀ n, stage n ⟶ stage (n + 1)
  projection : ∀ n, stage (n + 1) ⟶ quotient n
  retraction : ∀ n, stage (n + 1) ⟶ stage n
  section_ : ∀ n, quotient n ⟶ stage (n + 1)
  inclusion_retraction : ∀ n, inclusion n ≫ retraction n = 𝟙 _
  section_projection : ∀ n, section_ n ≫ projection n = 𝟙 _
  section_retraction : ∀ n, section_ n ≫ retraction n = 0
  inclusion_projection : ∀ n, inclusion n ≫ projection n = 0
  decomposition : ∀ n,
    retraction n ≫ inclusion n + projection n ≫ section_ n = 𝟙 _

namespace SplitModuleSequence
variable {S : Type u} [CommRing S] (F : SplitModuleSequence S)

/-- 概要：初期加群を零番目、各商を後続の直和成分に置く。
方針：自然数で場合分けする。
規約：成分 n+1 は n 番目の商。使われ方：直和の添字。 -/
abbrev piece : ℕ → ModuleCat.{u} S
  | 0 => F.stage 0
  | n + 1 => F.quotient n

/-- 概要：各有限段の直和座標。
方針：前段への戻しの座標と新しい商の座標を加える。
規約：値域は全成分の直和。使われ方：余極限への延長。 -/
def coordinates : ∀ n, F.stage n →ₗ[S] ⨁ i, F.piece i
  | 0 => DirectSum.lof S ℕ (fun i => F.piece i) 0
  | n + 1 => coordinates n ∘ₗ (F.retraction n).hom +
      DirectSum.lof S ℕ (fun i => F.piece i) (n + 1) ∘ₗ (F.projection n).hom

/-- 概要：直和座標は包含と整合する。
方針：包含の戻しは恒等、包含の商は零であることを使う。
規約：隣接段についての等式。使われ方：座標の cocone。 -/
theorem coordinates_inclusion (n : ℕ) :
    F.coordinates (n + 1) ∘ₗ (F.inclusion n).hom = F.coordinates n := by
  apply LinearMap.ext
  intro x
  have h₁ := congrArg (fun f => f.hom x) (F.inclusion_retraction n)
  have h₂ := congrArg (fun f => f.hom x) (F.inclusion_projection n)
  change (F.retraction n).hom ((F.inclusion n).hom x) = x at h₁
  change (F.projection n).hom ((F.inclusion n).hom x) = 0 at h₂
  simp only [coordinates, LinearMap.add_apply, LinearMap.comp_apply, h₁, h₂,
    map_zero, add_zero]

/-- 概要：第 n 段の座標は n より大きい成分では零である。
方針：再帰式と直和の単一成分の評価を使う。
規約：上限は段の番号。使われ方：微分が高さを下げることの証明。 -/
theorem coordinates_apply_eq_zero (n i : ℕ) (h : n < i) (x : F.stage n) :
    F.coordinates n x i = 0 := by
  induction n with
  | zero => exact DFinsupp.single_eq_of_ne (Nat.ne_of_gt h)
  | succ n ih =>
    change (F.coordinates n ((F.retraction n).hom x) +
      DirectSum.lof S ℕ (fun i => F.piece i) (n + 1) ((F.projection n).hom x)) i = 0
    rw [DFinsupp.add_apply, ih (Nat.lt_trans (Nat.lt_succ_self n) h)]
    exact zero_add _ |>.trans (DFinsupp.single_eq_of_ne (Nat.ne_of_gt h))

/-- 概要：座標を cocone にまとめる。
方針：隣接段の整合性から自然変換を構成する。
規約：頂点は初期加群と各商の直和。使われ方：余極限からの座標写像。 -/
def coordinateCocone : Cocone (Functor.ofSequence F.inclusion) where
  pt := ModuleCat.of S (⨁ i, F.piece i)
  ι := NatTrans.ofSequence (fun n => ModuleCat.ofHom (F.coordinates n)) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    exact F.coordinates_inclusion n)

variable (c : Cocone (Functor.ofSequence F.inclusion))

/-- 概要：直和の各成分を任意の cocone の頂点へ送る。
方針：初期成分は初期脚、商成分は切断と対応する脚の合成。
規約：切断に微分との可換性は要求しない。使われ方：座標の逆写像。 -/
def pieceMap : ∀ n, F.piece n →ₗ[S] c.pt
  | 0 => (c.ι.app 0).hom
  | n + 1 => (c.ι.app (n + 1)).hom ∘ₗ (F.section_ n).hom

/-- 概要：直和から cocone 頂点への線形写像。
方針：各成分の写像を直和の普遍性で延長する。
規約：初期成分と商成分を同じ番号で扱う。使われ方：直和表示の逆向き。 -/
def assemble : (⨁ i, F.piece i) →ₗ[S] c.pt :=
  DirectSum.toModule S ℕ _ (F.pieceMap c)

/-- 概要：座標から復元すると元の cocone の脚になる。
方針：段の帰納法と分裂の分解式を使う。
規約：任意の cocone に成立。使われ方：余極限上の逆等式。 -/
theorem assemble_coordinates (n : ℕ) :
    F.assemble c ∘ₗ F.coordinates n = (c.ι.app n).hom := by
  induction n with
  | zero =>
    apply LinearMap.ext
    intro x
    exact DirectSum.toModule_lof S (M := fun i => F.piece i) (φ := F.pieceMap c) 0 x
  | succ n ih =>
    ext x
    have hw := c.w (homOfLE (Nat.le_succ n))
    rw [Functor.ofSequence_map_homOfLE_succ] at hw
    have hd := congrArg (fun f => f.hom x) (F.decomposition n)
    change (F.inclusion n) ((F.retraction n) x) +
      (F.section_ n) ((F.projection n) x) = x at hd
    change F.assemble c (F.coordinates n ((F.retraction n) x) +
      DirectSum.lof S ℕ (fun i => F.piece i) (n + 1) ((F.projection n) x)) = _
    rw [map_add]
    have hs := DirectSum.toModule_lof S (M := fun i => F.piece i)
      (φ := F.pieceMap c) (n + 1) ((F.projection n).hom x)
    change F.assemble c (DirectSum.lof S ℕ (fun i => F.piece i) (n + 1)
      ((F.projection n).hom x)) = _ at hs
    rw [hs]
    have hi := LinearMap.congr_fun ih ((F.retraction n) x)
    change F.assemble c (F.coordinates n ((F.retraction n) x)) = _ at hi
    rw [hi]
    let a : F.stage n →ₗ[S] c.pt := (c.ι.app n).hom
    let b : F.stage (n + 1) →ₗ[S] c.pt := (c.ι.app (n + 1)).hom
    change a ((F.retraction n).hom x) + b ((F.section_ n).hom ((F.projection n).hom x)) = b x
    have hwx := congrArg (fun f => f.hom ((F.retraction n).hom x)) hw
    change (c.ι.app (n + 1)).hom ((F.inclusion n).hom ((F.retraction n).hom x)) =
      (c.ι.app n).hom ((F.retraction n).hom x) at hwx
    change b ((F.inclusion n).hom ((F.retraction n).hom x)) =
      a ((F.retraction n).hom x) at hwx
    rw [← hwx, ← map_add]
    exact congrArg b hd

/-- 概要：余極限の座標は切断された成分を対応する直和成分へ送る。
方針：余極限の脚の等式と切断の分裂式を使う。
規約：余極限の選択に依存しない。使われ方：直和表示の逆等式と基底の高さ。 -/
theorem desc_pieceMap (hc : IsColimit c) (n : ℕ) :
    (hc.desc F.coordinateCocone).hom ∘ₗ F.pieceMap c n =
      DirectSum.lof S ℕ (fun i => F.piece i) n := by
  cases n with
  | zero =>
    exact congrArg ModuleCat.Hom.hom (hc.fac F.coordinateCocone 0)
  | succ n =>
    ext x
    have hf := congrArg (fun f => f.hom ((F.section_ n) x))
      (hc.fac F.coordinateCocone (n + 1))
    have hr := congrArg (fun f => f.hom x) (F.section_retraction n)
    have hp := congrArg (fun f => f.hom x) (F.section_projection n)
    change (F.retraction n).hom ((F.section_ n).hom x) = 0 at hr
    change (F.projection n).hom ((F.section_ n).hom x) = x at hp
    change (hc.desc F.coordinateCocone) ((c.ι.app (n + 1)) ((F.section_ n) x)) =
      F.coordinates (n + 1) ((F.section_ n).hom x) at hf
    change (hc.desc F.coordinateCocone) ((c.ι.app (n + 1)) ((F.section_ n) x)) = _
    rw [hf]
    simp only [coordinates, LinearMap.add_apply, LinearMap.comp_apply, hr, hp,
      map_zero, zero_add]
    rfl

/-- 概要：分裂列の余極限は初期加群と各商の直和に線形同型である。
方針：座標と復元写像が、脚および直和成分上で互いに逆であることを示す。
規約：分裂は次数ごとに利用できる。使われ方：既存 semifree filtration からの基底構成。 -/
def linearEquiv (hc : IsColimit c) : c.pt ≃ₗ[S] ⨁ i, F.piece i :=
  LinearEquiv.ofLinearMap (hc.desc F.coordinateCocone).hom (F.assemble c)
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro x
      change (hc.desc F.coordinateCocone).hom
        (F.assemble c (DirectSum.lof S ℕ (fun i => F.piece i) n x)) = _
      rw [assemble, DirectSum.toModule_lof]
      exact LinearMap.congr_fun (F.desc_pieceMap c hc n) x)
    (by
      apply ModuleCat.hom_ext_iff.mp
      apply hc.hom_ext
      intro n
      change c.ι.app n ≫ ModuleCat.ofHom
        ((F.assemble c) ∘ₗ (hc.desc F.coordinateCocone).hom) = c.ι.app n ≫ 𝟙 _
      rw [Category.comp_id]
      apply ModuleCat.hom_ext
      change F.assemble c ∘ₗ ((hc.desc F.coordinateCocone).hom ∘ₗ (c.ι.app n).hom) = _
      rw [show (hc.desc F.coordinateCocone).hom ∘ₗ (c.ι.app n).hom = F.coordinates n from
        congrArg ModuleCat.Hom.hom (hc.fac F.coordinateCocone n)]
      exact F.assemble_coordinates c n)

/-- 概要：余極限同型は各脚を有限段の座標へ送る。
方針：余極限の因子分解等式を評価する。
規約：任意の段と元について成立。使われ方：高さの上限。 -/
theorem linearEquiv_leg (hc : IsColimit c) (n : ℕ) (x : F.stage n) :
    F.linearEquiv c hc ((c.ι.app n).hom x) = F.coordinates n x :=
  congrArg (fun f => f.hom x) (hc.fac F.coordinateCocone n)

/-- 概要：余極限同型の逆は各直和成分を切断された商へ送る。
方針：復元写像の定義と直和の普遍性を展開する。
規約：零成分では初期段の脚。使われ方：基底ベクトルの具体形。 -/
theorem linearEquiv_symm_lof (hc : IsColimit c) (n : ℕ) (x : F.piece n) :
    (F.linearEquiv c hc).symm (DirectSum.lof S ℕ (fun i => F.piece i) n x) =
      F.pieceMap c n x := by
  change F.assemble c (DirectSum.lof S ℕ (fun i => F.piece i) n x) = _
  exact DirectSum.toModule_lof S (M := fun i => F.piece i) (φ := F.pieceMap c) n x

end SplitModuleSequence
end SerrePositivity.InfinityCategories.Project.DerivedCategories
