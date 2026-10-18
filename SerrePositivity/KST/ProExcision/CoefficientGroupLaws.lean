module
public import SerrePositivity.KST.ProExcision.SimplicialIdealData

/-!
# 係数群の写像の恒等・合成法則

概要：イデアルの列群と三角ブロック群の係数写像は恒等と合成を保つ。
方針：群準同型・単位・実行列の値の外延性で定義を評価する。
規約：KST Lemma 4.16 の関手的な単体化。
使われ方：次数ごとの実群を単体的群に束ねる。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R R' R'' : Type u} [Ring R] [Ring R'] [Ring R'']

/-- 概要：イデアル内の列の係数写像は恒等を保つ。
方針：ベクトルの各係数の定義を評価する。
規約：KST 4.16。使われ方：単体的な列群の恒等法則。 -/
lemma idealVectorMap_id (J : TwoSidedIdeal R) (ι : Type v) :
    idealVectorMap J J ι (RingHom.id R) (fun _ hx ↦ hx) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro v
  rfl

/-- 概要：イデアル内の列の係数写像は合成を保つ。
方針：ベクトルの各係数で写像の合成を評価する。
規約：KST 4.16。使われ方：単体的な列群の合成法則。 -/
lemma idealVectorMap_comp (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R') (J'' : TwoSidedIdeal R'') (ι : Type v)
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (g : R' →+* R'') (hg : ∀ x, x ∈ J' → g x ∈ J'') :
    (idealVectorMap J' J'' ι g hg).comp (idealVectorMap J J' ι f hf) =
      idealVectorMap J J'' ι (g.comp f) (fun x hx ↦ hg _ (hf x hx)) := by
  apply MonoidHom.ext
  intro v
  rfl

/-- 概要：三角ブロック群の係数写像は恒等を保つ。
方針：単位と行列の値で恒等写像を評価する。
規約：KST 4.16。使われ方：単体的な実ブロック群の恒等法則。 -/
lemma triangularBlockGroupMap_id (n m : ℕ) (J : TwoSidedIdeal R) :
    triangularBlockGroupMap n m J J (RingHom.id R) (fun _ hx ↦ hx) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  rfl

/-- 概要：三角ブロック群の係数写像は合成を保つ。
方針：単位の実行列の成分に順に係数写像を適用する。
規約：KST 4.16。使われ方：単体的な実ブロック群の合成法則。 -/
lemma triangularBlockGroupMap_comp (n m : ℕ)
    (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R') (J'' : TwoSidedIdeal R'')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (g : R' →+* R'') (hg : ∀ x, x ∈ J' → g x ∈ J'') :
    (triangularBlockGroupMap n m J' J'' g hg).comp (triangularBlockGroupMap n m J J' f hf) =
      triangularBlockGroupMap n m J J'' (g.comp f) (fun x hx ↦ hg _ (hf x hx)) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  apply Units.ext
  rfl

end SerrePositivity.KST.ProExcision
