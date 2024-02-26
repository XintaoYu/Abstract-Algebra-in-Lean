import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 引论

#check 1 -- Nat
#check Nat -- Type
#check 1 + 1 = 2 -- Prop
#check fun x ↦ x + 1 -- Nat → Nat
#check fun (x : Float) ↦ x + 1 -- Float → Float
#check fun x ↦ x

#check Nat.add  -- Nat → Nat → Nat
#check (Nat.add 1) -- Nat → Nat
#check (Nat.add 1 1) -- Nat
#eval Nat.add 1 1 -- 2

example : 1 + 1 = 2 := rfl

-- example : 1 + 1 = Nat.add 1 1 := rfl
-- example : Nat.add 1 1 = Nat.succ (Nat.succ Nat.zero) := rfl
-- example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat'): Nat'

def one' : Nat' := Nat'.succ Nat'.zero
def two' : Nat' := Nat'.succ (Nat'.succ Nat'.zero)

def Nat'.add (n k : Nat') : Nat' :=
  match k with
  | Nat'.zero => n
  | Nat'.succ k' => Nat'.succ  (Nat'.add n k')

example: Nat'.add one' one' = two' := rfl
-- #eval Nat'.add one' one' = two'


#check Nat.dvd_trans
-- Nat.dvd_trans {a b c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c
#check Nat.dvd_mul_right
-- Nat.dvd_mul_right (a b : ℕ) : a ∣ a * b

example : ∀ (m n k : Nat), m ∣ n → m ∣ n * k :=
  fun m n k h ↦ Nat.dvd_trans h (Nat.dvd_mul_right n _)

example (m n k: Nat) : m ∣ n → m ∣ n * k :=
  fun h ↦ Nat.dvd_trans h (Nat.dvd_mul_right n _)

example (m n k: Nat) (h : m ∣ n) : m ∣ n * k :=
  Nat.dvd_trans h (Nat.dvd_mul_right n _)

example : ∀ (m n k : Nat), m ∣ n → m ∣ n * k := by
  intro m n k h
  apply dvd_mul_of_dvd_left h

example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  repeat rw [pow_two]
  rw [add_mul, mul_add, mul_add]
  rw [mul_comm b a, ← add_assoc, add_assoc (a * a), ← two_mul, ← mul_assoc]


example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  calc
    _ = a * a + a * b + b * a + b * b := by
      repeat rw [pow_two]
      rw [add_mul, mul_add, mul_add, ← add_assoc]
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by
      repeat rw [← pow_two]
      rw [mul_comm b a, add_assoc (a ^ 2), ← two_mul, ← mul_assoc]

example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example : 1 + 2  = 3 := rfl



-- 简单的等式的证明


-- 等式的证明，实际上就是证明等号两边相等。
-- 对于lean而言，“相等”意味着完全相同。例如a+b和b+a是不相等的。
-- 最基本的证明策略，就是利用变换，使得等号两边完全相同。
-- 在lean中，我们利用rw(rewrite)这个tactic来进行改写。在证明过程中，我们要注意右侧Lean Inforview给出的当前目标式，基于其进行改写。

example(h:a=c) (h':b=c):a=b:=by
  rw [h]--利用条件h进行改写
  rw [h']--利用条件h'进行改写

-- 在这个最简单的例子中，我们依据h和h'两个给出的条件，分别将a和b改写成c，以完成等式的证明，方法是在rw后的[]内输入对应的条件


-- 实际上，除了给出的条件，我们还需要利用一些已有的定理来进行改写，下面对此进行简单的讲解：

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]--乘法交换律
  rw [mul_assoc b c a]--乘法结合律
  rw [mul_comm c a]

-- 在这个例子中，我们利用乘法交换律和结合律对目标式进行改写，最终使等号两端相等。

-- 为了更好地lean中浩如烟海的定理，我们首先介绍#check。在其后输入定理的名字，VScode界面右侧的Lean Inforview栏目会显示定理的有关信息

#check mul_comm
-- ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a(从Lean Infoview中复制，下同)
#check mul_assoc
-- ∀ {G : Type u_1} [inst : Semigroup G] (a b c : G), a * b * c = a * (b * c)

-- 使用定理进行rw时，常常需要提供一些参数，以帮助lean确定改写的对象。当不给出参数时，lean将自动寻找满足条件的对象进行改写，但这并不一定准确。
-- 再次取前面的例子为例，我们看其中具体的步骤。

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]--乘法交换律
-- 在这步中，我们通过在定理后加入参数并用空格隔开的方式，告诉lean要交换的是b和c。
  rw [mul_assoc b c a]--乘法结合律
-- 在这步中，我们通过参数确定要将c*b*a改写为c*(b*a)
  rw [mul_comm c a]

-- 通过这个例子，我们还可以发现lean的一个书写规则：当多个元素一起进行计算时，自动将前两个看作一组，但省略括号。
-- 例如：a*b*c实际上为(a*b)*c,当我们对其中b和c利用乘法交换律进行交换时，lean就会报错，因为（a*b）是一个整体。

-- 在一些情况下，我们需要定理的“逆用”
-- 在等式证明中利用的定理，常常被表达成一个等式的形式，例如

#check mul_assoc
-- ∀ {G : Type u_1} [inst : Semigroup G] (a b c : G), a * b * c = a * (b * c)

-- 在一般情况下，lean施行的是将等号左侧的形式变成等号右侧的形式的改写。
-- 但在一些情况下，我们需要将右侧的形式改写成左侧的形式，方法是在定理之前打出"← "（一个左箭头再加一个空格）。
-- 具体的输入方法是依次输入“\”“l”和一个空格（此时已经包含了后面的一个空格，不需再输入）。

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- 其中第二步“逆用”乘法结合律将a * (b * f)改写成a * b * f

-- 通过这个例子，我们还可以知道rw的一种简便写法，当要进行多步的rewrite时，可以将不同步依据的定理（必要时包括参数）输入一个rw的[]内，并用逗号隔开。


-- 下面，我们介绍两个更加自动化的tactic。它们在特定的情形下将带来极大的便利。


-- 当要证明的等式中仅含有纯数字时，我们可以使用norm_num这个tactic

example : 1 + 1 = 2 := by
  norm_num


-- 当要证明的等式中仅需要加减乘除的化简时，我们可以使用ring这个tactic

variable (a b c d e f : ℝ)

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

-- 可以发现，ring这个tactic十分强大，可以一步完成这些证明。其实，让我们来看这些式子，我们也会认为它们相等是非常自然的。
-- 实际上，我们可以去思考那些我们认为很自然的结果背后的原理。实际上，(R,+,*)为含幺交换环，根据环的性质可以进行“简单”的加减乘除的化简。
-- ring这个tactic，就是利用环的性质进行有关的证明。(R,+,*)为含幺交换环，根据环的性质可以进行“简单”的加减乘除的化简。

-- ring还有一个更强的版本ring_nf。当ring无法成功时可以尝试这个tactic。


-- 下面，我们介绍两个可以使证明的代码更加清晰简练的tactic。我们通过引论中出现过的一个例子来介绍。

example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  calc
    _ = a * a + a * b + b * a + b * b := by
      repeat rw [pow_two]
      rw [add_mul, mul_add, mul_add, ← add_assoc]
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by
      repeat rw [← pow_two]
      rw [mul_comm b a, add_assoc (a ^ 2), ← two_mul, ← mul_assoc]

-- calc，可以进入“计算模式”，将化简过程分步显示。在例子中，每一步的 _ 指代上一步的结果（第一步的 _ 则指代等号左边的式子）。在每一步的下方，需要有这一步对应的证明。

-- repeat，将使lean重复进行后面的操作，直到目标式中不再有可以执行操作的对象。


-- 在本部分最后，我们介绍两个特殊的tactic。

-- sorryc，将使lean暂时忽略一个命题的证明，并直接认为这个命题是正确的。这个tacitc主要用于布置习题，以免lean对于没有证明的命题报错。

theorem hard : FermatLastTheorem :=
  sorry


-- apply?，这个tactic会令lean搜索tactic和定理的库，并给出证明建议。
-- 使用这个tactic时程序需要一定的时间进行搜索，请耐心等待。
-- 这个tactic不设置示例，大家可以在自己的VScode中对任意的习题进行尝试。
