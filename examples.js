/* 內建範例（網頁與測試共用）。expect 是測試用的預期結果。 */
(function (root) {
const EXAMPLES = [
{
  id: 'liars', label: '三人互指說謊', expect: ['proved'],
  puzzle: 'A 說 B 在說謊，B 說 C 在說謊，C 說 A、B 都在說謊。請問到底誰在說謊？',
  lean: `/-
【題目】A 說 B 在說謊，B 說 C 在說謊，C 說 A、B 都在說謊。誰在說謊？
【結論】A 和 C 在說謊，只有 B 說真話。
-/

theorem who_is_lying
    (a b c : Bool)              -- a / b / c 為 true 代表 A / B / C 說的是真話
    (hA : a = !b)               -- A 說：B 在說謊
    (hB : b = !c)               -- B 說：C 在說謊
    (hC : c = (!a && !b))       -- C 說：A、B 都在說謊
    : a = false ∧ b = true ∧ c = false := by decide
`,
},
{
  id: 'gods', label: '史上最難邏輯謎題（三神）', expect: ['proved'],
  puzzle: '三位神祇 A、B、C 分別是真實、虛謊、任性之神，只會回答 da 或 ja（不知道哪個是「是」）。用三條是非題找出祂們的身分。',
  lean: `/-
【題目】三位神祇 A、B、C 分別是「真實、虛謊、任性」。真實只說真話，虛謊只說假話，
任性隨機回答。祂們只回答 da 或 ja，而你不知道哪個字代表「是」。只能問三條是非題，
每次問一位神，找出三位神的身分。
【結論】有必勝問法。一律用巢狀問句「如果我問你『P 是真的嗎？』，你會回答 ja 嗎？」
第 1 題問 B：P =「A 是任性之神」。答 ja 就改問 C，答 da 就改問 A（這位保證不是任性之神，稱為 X）。
第 2 題問 X：P =「你是虛謊之神」。答 ja → X 是虛謊，答 da → X 是真實。
第 3 題問 X：P =「B 是任性之神」。答 ja → B 是任性，答 da → 剩下那位是任性。
不管銅板怎麼擲、da 是什麼意思，全部 96 種情況都能認出三位神。
-/

inductive God | truth | liar | random     -- 真實、虛謊、任性
  deriving DecidableEq
inductive Word | da | ja
  deriving DecidableEq

/-- 神 g 心裡對「p 是真的嗎？」表達的是不是「是」。coin = 任性之神這一題擲的銅板 -/
def saysYes (g : God) (coin p : Bool) : Bool :=
  match g with
  | .truth => p
  | .liar => !p
  | .random => coin

/-- 神實際說出口的字。daYes = true 代表 da 的意思是「是」 -/
def answer (g : God) (daYes coin p : Bool) : Word :=
  if saysYes g coin p = daYes then .da else .ja

/-- 巢狀問句：「如果我問你『p 是真的嗎？』，你會回答 ja 嗎？」 -/
def ask (g : God) (daYes coin p : Bool) : Word :=
  answer g daYes coin (answer g daYes coin p == .ja)

/-- 第 1 題問 B：「A 是任性之神」 -/
def r1 (a b : God) (daYes c1 : Bool) : Word :=
  ask b daYes c1 (a == .random)

/-- X：接下來要問的神。r1 = ja 就問 C，否則問 A -/
def x (a b c : God) (daYes c1 : Bool) : God :=
  if r1 a b daYes c1 = .ja then c else a

/-- 第 2 題問 X：「你是虛謊之神」 -/
def r2 (a b c : God) (daYes c1 c2 : Bool) : Word :=
  ask (x a b c daYes c1) daYes c2 (x a b c daYes c1 == .liar)

/-- 第 3 題問 X：「B 是任性之神」 -/
def r3 (a b c : God) (daYes c1 c3 : Bool) : Word :=
  ask (x a b c daYes c1) daYes c3 (b == .random)

theorem three_gods_strategy
    (a b c : God)                          -- A、B、C 的真實身分
    (daYes : Bool)                         -- da 是不是「是」的意思（你不知道）
    (c1 c2 c3 : Bool)                      -- 任性之神三次擲銅板的結果（你不知道）
    (hDiff : a ≠ b ∧ a ≠ c ∧ b ≠ c)        -- 三位神身分各不相同
    : x a b c daYes c1 ≠ .random                                                       -- X 一定不是任性之神
    ∧ x a b c daYes c1 = (if r2 a b c daYes c1 c2 = .ja then God.liar else God.truth)  -- 第 2 題認出 X
    ∧ ((r3 a b c daYes c1 c3 = .ja) ↔ b = .random)                                     -- 第 3 題認出任性之神
    := by decide
`,
},
{
  id: 'wrong', label: '答錯會怎樣？', expect: ['refuted'],
  puzzle: '同一題三人互指說謊，但這次故意主張「A 說真話」。',
  lean: `/-
【題目】A 說 B 在說謊，B 說 C 在說謊，C 說 A、B 都在說謊。誰在說謊？
【結論】（故意寫錯）只有 A 說真話，B 和 C 在說謊。
-/

theorem who_is_lying
    (a b c : Bool)              -- a / b / c 為 true 代表 A / B / C 說的是真話
    (hA : a = !b)               -- A 說：B 在說謊
    (hB : b = !c)               -- B 說：C 在說謊
    (hC : c = (!a && !b))       -- C 說：A、B 都在說謊
    : a = true ∧ b = false ∧ c = false := by decide
`,
},
{
  id: 'paradox', label: '說謊者悖論', expect: ['vacuous'],
  puzzle: '有個人說：「我現在說的這句話是假的。」他說的是真話還是假話？',
  lean: `/-
【題目】有個人說：「我現在說的這句話是假的。」他說的是真話嗎？
【結論】他說的是真話。
-/

theorem liar_paradox
    (p : Bool)            -- p 為 true 代表這句話是真的
    (h : p = !p)          -- 這句話的內容：「這句話是假的」
    : p = true := by decide
`,
},
{
  id: 'race', label: '賽跑名次', expect: ['proved'],
  puzzle: '甲、乙、丙、丁四人賽跑，沒有同名次。甲不是第一名；乙剛好比甲快一名；丙比丁慢；丁不是第一名。四個人各是第幾名？',
  lean: `/-
【題目】甲、乙、丙、丁四人賽跑，沒有同名次。甲不是第一名；乙剛好比甲快一名；
丙比丁慢；丁不是第一名。四個人各是第幾名？
【結論】乙第一、甲第二、丁第三、丙第四。
-/

theorem race_order
    (jia yi bing ding : Fin 4)                   -- 名次：0 = 第一名 … 3 = 第四名
    (hDiff : jia ≠ yi ∧ jia ≠ bing ∧ jia ≠ ding ∧ yi ≠ bing ∧ yi ≠ ding ∧ bing ≠ ding)  -- 沒有同名次
    (h1 : jia ≠ 0)                               -- 甲不是第一名
    (h2 : yi.val + 1 = jia.val)                  -- 乙剛好比甲快一名
    (h3 : bing.val > ding.val)                   -- 丙比丁慢
    (h4 : ding ≠ 0)                              -- 丁不是第一名
    : yi = 0 ∧ jia = 1 ∧ ding = 2 ∧ bing = 3 := by decide
`,
},
{
  id: 'thief', label: '誰偷了蛋糕', expect: ['proved'],
  puzzle: '小明、小華、小美三人中有一人偷吃了蛋糕。小明說：「不是我。」小華說：「是小美。」小美說：「小華在說謊。」三人之中只有一個人說真話。是誰偷吃的？',
  lean: `/-
【題目】小明、小華、小美三人中有一人偷吃了蛋糕。小明說：「不是我。」
小華說：「是小美。」小美說：「小華在說謊。」三人之中只有一個人說真話。是誰偷吃的？
【結論】偷吃的是小明；只有小美說真話。
-/

inductive Kid | ming | hua | mei          -- 小明、小華、小美
  deriving DecidableEq

theorem cake_thief
    (thief : Kid)                                    -- 偷吃蛋糕的人
    (sMing sHua sMei : Bool)                         -- 三個人說的話是真是假
    (h1 : sMing = (thief != .ming))                  -- 小明說：不是我
    (h2 : sHua = (thief == .mei))                    -- 小華說：是小美
    (h3 : sMei = !sHua)                              -- 小美說：小華在說謊
    (hOne : sMing.toNat + sHua.toNat + sMei.toNat = 1)   -- 只有一個人說真話
    : thief = .ming ∧ sMei = true := by decide
`,
},
];
if (typeof module !== 'undefined' && module.exports) module.exports = EXAMPLES;
else root.LEAN_EXAMPLES = EXAMPLES;
})(typeof window !== 'undefined' ? window : globalThis);
