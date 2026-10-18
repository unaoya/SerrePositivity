module
public import SerrePositivity.KST.ProExcision.ConstructionA5
public import SerrePositivity.KST.ProExcision.TensorAugmentationNaturality
public import SerrePositivity.KST.ProExcision.LinearizedGroupProductNaturality
public import SerrePositivity.KST.ProExcision.DiscreteActionNaturality

/-!
# 非可換標的に対する μ 版 A.5 の外部 G 同変性

概要：因子内の同変な入力から構成した実 (m+m′+1) 次ホモトピーは外部 G 同変。
方針：厳密化、正規化、差のテンソル、AW・shuffle、区間復元の自然性を各作用元へ適用する。
規約：KST Construction A.5 の右辺の augmentation 補正 C(φ)+C(φ′)−C(e_H)。
原典の一般文言との差として P,Q,H,μ と因子内の入力を明示する。H は非可換でよい。
使われ方：非可換ブロック行列群に対する Lemma 4.16。結論の同変性を入力に含めない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {G T P Q H : Type u} [Monoid G] [Group T] [Group P] [Group Q] [Group H]
variable {ρT : G →* Monoid.End T} {ρP : G →* Monoid.End P}
variable {ρQ : G →* Monoid.End Q} {ρH : G →* Monoid.End H}

/-- 概要：μ 版 A.5 の実ホモトピーは外部 G 同変。
方針：採用済みの各入力の同変性を構成全体の自然性へ渡す。
規約：KST A.5 の augmentation 補正、因子内のホモトピー、非可換な H。
使われ方：C(ψ) の補正式から C(φ) と C(e) の同変な比較を得る。 -/
lemma constructionA5_equivariant
    (d : EquivariantGroupProductData ρT ρP ρQ ρH) (m m' : ℕ)
    (h : ConstructionA5Input d m m') :
    LinearizedCylinderEquivariant
      (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of H) ρH)
      (constructionA5 d.toGroupProductData m m' h.first h.second).h := by
  intro n a
  have hf := groupLinearizedMap_equivariant ρT ρP d.α d.α_equivariant
  have hg := groupLinearizedMap_equivariant ρT ρQ d.β d.β_equivariant
  have he := groupLinearizedMap_equivariant ρT ρP (1 : T →* P)
    (by intro b t; simp only [MonoidHom.one_apply, map_one])
  have he' := groupLinearizedMap_equivariant ρT ρQ (1 : T →* Q)
    (by intro b t; simp only [MonoidHom.one_apply, map_one])
  have hh := h.first.strictificationHomotopy_equivariant hf h.first_equivariant
  have hk := h.second.strictificationHomotopy_equivariant hg h.second_equivariant
  have hn := linearizedTensorAugmentationMHomotopy_naturality h.first h.second
    (linearizedDiagonal (nerve (SingleObj T))) (linearizedGroupProduct d.μ)
    (nerveMap (SingleObj.mapHom T T (ρT a)))
    (nerveMap (SingleObj.mapHom T T (ρT a)))
    (nerveMap (SingleObj.mapHom T T (ρT a)))
    (nerveMap (SingleObj.mapHom P P (ρP a)))
    (nerveMap (SingleObj.mapHom Q Q (ρQ a)))
    (nerveMap (SingleObj.mapHom H H (ρH a)))
    (hf.discrete_naturality ρT ρP a) (hg.discrete_naturality ρT ρQ a)
    (he.discrete_naturality ρT ρP a) (he'.discrete_naturality ρT ρQ a)
    (h.first_strictified_equivariant.discrete_naturality ρT ρP a)
    (h.second_strictified_equivariant.discrete_naturality ρT ρQ a)
    (hh.discrete_naturality ρT ρP a) (hk.discrete_naturality ρT ρQ a)
    (linearizedDiagonal_naturality (nerveMap (SingleObj.mapHom T T (ρT a))))
    (linearizedGroupProduct_naturality d.μ d.μ (ρP a) (ρQ a) (ρH a) (d.μ_equivariant a))
  exact congrArg (fun f ↦ f.app n) hn

/-- 概要：μ 版 A.5 の実区間射を作用 bar へ渡せる同変界面に束ねる。
方針：構成した実ホモトピーに証明済みの外部 G 同変性を付ける。
規約：KST A.5 の右辺の augmentation 補正、非可換標的と因子内の入力。
使われ方：Lemma 4.16 での同変な相殺および A.4 の bar 比較。 -/
def constructionA5EquivariantCylinderMap
    (d : EquivariantGroupProductData ρT ρP ρQ ρH) (m m' : ℕ)
    (h : ConstructionA5Input d m m') :
    EquivariantLinearizedCylinderMap
      (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of H) ρH) where
  h := (constructionA5 d.toGroupProductData m m' h.first h.second).h
  equivariant := constructionA5_equivariant d m m' h

end SerrePositivity.KST.ProExcision
