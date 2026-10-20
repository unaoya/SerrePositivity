module

public import SerrePositivity.EInfinity.Hammock.WordIntersection
public import SerrePositivity.EInfinity.Hammock.WordFactorization

/-!
# 元の列の交わりから二つの包含への射

概要：元の列の交わりの包含は、両方の元の包含を通して厳密に因子分解する。
方針：像の包含と単射な語の写像の持ち上げを用いる。
規約：元の語と元の列の写像を保持する。
使われ方：proper 図式の原像の重なりの回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

variable {a b c : Word} (f : a ⟶ c) (g : b ⟶ c)

def intersectionLeft (hf : Function.Injective f.orderHom) : intersection f g ⟶ a :=
  (factorEmbedding f hf (intersectionInclusion f g) (by
    rw [intersectionInclusion_range]; exact Set.inter_subset_left)).val

def intersectionRight (hg : Function.Injective g.orderHom) : intersection f g ⟶ b :=
  (factorEmbedding g hg (intersectionInclusion f g) (by
    rw [intersectionInclusion_range]; exact Set.inter_subset_right)).val

lemma intersectionLeft_fac (hf : Function.Injective f.orderHom) :
    intersectionLeft f g hf ≫ f = intersectionInclusion f g :=
  (factorEmbedding f hf (intersectionInclusion f g) (by
    rw [intersectionInclusion_range]; exact Set.inter_subset_left)).property

lemma intersectionRight_fac (hg : Function.Injective g.orderHom) :
    intersectionRight f g hg ≫ g = intersectionInclusion f g :=
  (factorEmbedding g hg (intersectionInclusion f g) (by
    rw [intersectionInclusion_range]; exact Set.inter_subset_right)).property

lemma intersectionLeft_injective (hf : Function.Injective f.orderHom) :
    Function.Injective (intersectionLeft f g hf).orderHom := by
  intro i j hij
  apply intersectionInclusion_injective f g
  have he := congrArg (fun h : intersection f g ⟶ c => h.orderHom i)
    (intersectionLeft_fac f g hf)
  have he' := congrArg (fun h : intersection f g ⟶ c => h.orderHom j)
    (intersectionLeft_fac f g hf)
  exact he.symm.trans ((congrArg f.orderHom hij).trans he')

lemma intersectionRight_injective (hg : Function.Injective g.orderHom) :
    Function.Injective (intersectionRight f g hg).orderHom := by
  intro i j hij
  apply intersectionInclusion_injective f g
  have he := congrArg (fun h : intersection f g ⟶ c => h.orderHom i)
    (intersectionRight_fac f g hg)
  have he' := congrArg (fun h : intersection f g ⟶ c => h.orderHom j)
    (intersectionRight_fac f g hg)
  exact he.symm.trans ((congrArg g.orderHom hij).trans he')

lemma intersection_length_le_left (hf : Function.Injective f.orderHom) :
    (intersection f g).length ≤ a.length := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective _ (intersectionLeft_injective f g hf)

end SerrePositivity.EInfinity.Hammock.Word
