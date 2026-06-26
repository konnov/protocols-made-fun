const fs = require("fs");
const path = require("path");
const matter = require("gray-matter");
const MarkdownIt = require("markdown-it");
const markdownItAnchor = require("markdown-it-anchor");
const markdownItAttrs = require("markdown-it-attrs");
const markdownItEmoji = require("markdown-it-emoji").full;
const markdownItFootnote = require("markdown-it-footnote");
const hljs = require("highlight.js");

const siteUrl = "https://protocols-made-fun.com";
const outputDir = "_site";
const embedCachePath = path.join(__dirname, ".cache", "github-embeds.json");

const feedUtm = {
  utm_source: "protocols_made_fun",
  utm_medium: "feed",
  utm_campaign: "pmf_feed",
};

function registerSmallLanguage(name, keywords, options = {}) {
  const aliases = options.aliases || [];
  const comments = options.comments || [hljs.C_LINE_COMMENT_MODE, hljs.C_BLOCK_COMMENT_MODE];
  const extraContains = options.contains || [];
  hljs.registerLanguage(name, () => ({
    name,
    aliases: [name, ...aliases],
    keywords,
    contains: [
      hljs.QUOTE_STRING_MODE,
      hljs.NUMBER_MODE,
      ...comments,
      ...extraContains,
    ],
  }));
}

registerSmallLanguage(
  "tlaplus",
  "ASSUME ASSUMPTION AXIOM BOOLEAN CASE CHOOSE CONSTANT CONSTANTS DOMAIN ELSE ENABLED EXCEPT EXTENDS FALSE IF IN INSTANCE LET LOCAL MODULE Nat OTHER SF_ STRING SUBSET THEN THEOREM TRUE UNCHANGED UNION VARIABLE VARIABLES WF_ WITH Cardinality Len Seq",
  {
    aliases: ["tla", "tla+", "pluscal"],
    comments: [hljs.COMMENT(/\\\*/, /$/), hljs.COMMENT(/\(\*/, /\*\)/)],
    contains: [
      {
        scope: "keyword",
        match: /\\A|\\E|\\in|\\notin|\\subseteq|\\cup|\\cap|UNCHANGED|ENABLED|DOMAIN|SUBSET/,
      },
      {
        scope: "operator",
        match: /==|=>|<=>|\/\\|\\\/|\.\.|#|<=|>=|=|\+|-|\*|\/|~|\^/,
      },
      {
        scope: "title.function",
        match: /^[A-Za-z_][A-Za-z0-9_]*(?=\s*==)/,
      },
      {
        scope: "literal",
        match: /\b(?:TRUE|FALSE)\b/,
      },
    ],
  },
);
registerSmallLanguage(
  "quint",
  "module import from export as type assume const var val def pure nondet action temporal run all any if else match and or not implies iff Set Map List Bool Int Nat str true false",
);
registerSmallLanguage(
  "lean",
  "abbrev axiom by class def deriving else example extends false forall fun have if import in inductive infix instance let macro match namespace opaque open partial private protected theorem true universe variable where with",
  {
    comments: [hljs.COMMENT("--", "$")],
  },
);

function escapeHtml(value) {
  return String(value ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function escapeXml(value) {
  return escapeHtml(value).replace(/'/g, "&apos;");
}

function dateFor(data) {
  const raw = data.date || data.page?.date;
  return raw instanceof Date ? raw : new Date(raw);
}

function dateParts(date) {
  return {
    year: String(date.getFullYear()).padStart(4, "0"),
    month: String(date.getMonth() + 1).padStart(2, "0"),
    day: String(date.getDate()).padStart(2, "0"),
  };
}

function categoriesFor(data) {
  const categories = data.categories || [];
  if (Array.isArray(categories)) {
    return categories.filter(Boolean).map(String);
  }
  return String(categories)
    .split(/\s+/)
    .filter(Boolean);
}

function slugFromInputPath(inputPath) {
  const base = path.basename(inputPath, path.extname(inputPath));
  return base.replace(/^\d{4}-\d{2}-\d{2}-/, "");
}

function postOldUrlFromData(data) {
  const date = dateFor(data);
  const parts = dateParts(date);
  const slug = slugFromInputPath(data.page.inputPath);
  const categoryPath = categoriesFor(data).join("/");
  const prefix = categoryPath ? `/${categoryPath}` : "";
  return `${prefix}/${parts.year}/${parts.month}/${parts.day}/${slug}.html`;
}

function postUrlFromData(data) {
  return `/${slugFromInputPath(data.page.inputPath)}.html`;
}

function rootPageUrl(inputPath) {
  const base = path.basename(inputPath, path.extname(inputPath));
  if (base === "index") {
    return "/";
  }
  return `/${base}.html`;
}

function loadPostMap() {
  const byFile = new Map();
  const byDateSlug = new Map();
  const byOldUrl = new Map();
  for (const file of fs.readdirSync(path.join(__dirname, "_posts"))) {
    if (!file.endsWith(".md")) {
      continue;
    }
    const inputPath = `_posts/${file}`;
    const parsed = matter.read(path.join(__dirname, inputPath));
    const data = { ...parsed.data, page: { inputPath } };
    const url = postUrlFromData(data);
    const oldUrl = postOldUrlFromData(data);
    byFile.set(inputPath, url);
    byDateSlug.set(file.replace(/\.md$/, ""), url);
    byOldUrl.set(oldUrl, url);
  }
  return { byFile, byDateSlug, byOldUrl };
}

const postMap = loadPostMap();

function linkUrl(target) {
  const cleaned = String(target).replace(/^['"]|['"]$/g, "");
  if (postMap.byFile.has(cleaned)) {
    return postMap.byFile.get(cleaned);
  }
  if (cleaned.startsWith("_posts/")) {
    return postMap.byFile.get(cleaned) || cleaned;
  }
  if (cleaned.endsWith(".md") || cleaned.endsWith(".html")) {
    return rootPageUrl(cleaned);
  }
  return cleaned;
}

function relativeUrl(input) {
  const value = String(input ?? "");
  if (!value || value.startsWith("http://") || value.startsWith("https://") || value.startsWith("mailto:") || value.startsWith("javascript:")) {
    return value;
  }
  if (/^(contact|datenschutz|impressum|disclaimer|about)\/?$/.test(value)) {
    return `/${value.replace(/\/$/, "")}.html`;
  }
  return value.startsWith("/") ? value : `/${value}`;
}

function absoluteUrl(input) {
  const value = String(input ?? "");
  if (value.startsWith("http://") || value.startsWith("https://")) {
    return value;
  }
  return `${siteUrl}${relativeUrl(value)}`;
}

function canonicalizeInternalUrl(input, baseUrl = siteUrl) {
  const original = String(input ?? "");
  if (!original.trim()) {
    return original;
  }
  try {
    const raw = original
      .replace(/&amp;/g, "&")
      .replace(/&#38;/g, "&");
    const url = new URL(raw, baseUrl || siteUrl);
    if (!["http:", "https:"].includes(url.protocol)) {
      return original;
    }
    if (url.hostname !== new URL(siteUrl).hostname) {
      return original;
    }
    const shortPath = postMap.byOldUrl.get(url.pathname);
    if (!shortPath) {
      return original;
    }
    url.pathname = shortPath;
    if (/^https?:\/\//.test(raw)) {
      return url.toString();
    }
    return `${url.pathname}${url.search}${url.hash}`;
  } catch {
    return original;
  }
}

function canonicalizeInternalHtml(input, baseUrl = siteUrl) {
  return String(input ?? "").replace(/(\b(?:href|src)\s*=\s*)(["'])(.*?)\2/gi, (_match, prefix, quote, url) => {
    return `${prefix}${quote}${escapeHtml(canonicalizeInternalUrl(url, baseUrl))}${quote}`;
  });
}

function feedUtmUrl(input, baseUrl = siteUrl) {
  const original = canonicalizeInternalUrl(input, baseUrl);
  if (!original.trim()) {
    return original;
  }
  try {
    const raw = original
      .replace(/&amp;/g, "&")
      .replace(/&#38;/g, "&");
    const url = new URL(raw, baseUrl || siteUrl);
    if (!["http:", "https:"].includes(url.protocol)) {
      return original;
    }
    for (const [key, value] of Object.entries(feedUtm)) {
      if (!url.searchParams.has(key)) {
        url.searchParams.append(key, value);
      }
    }
    return url.toString();
  } catch {
    return original;
  }
}

function feedUtmHtml(input, baseUrl = siteUrl) {
  return String(input ?? "").replace(/(\b(?:href|src)\s*=\s*)(["'])(.*?)\2/gi, (_match, prefix, quote, url) => {
    return `${prefix}${quote}${escapeHtml(feedUtmUrl(url, baseUrl))}${quote}`;
  });
}

function listValues(value) {
  if (!value) {
    return [];
  }
  if (Array.isArray(value)) {
    return value.filter(Boolean).map(String);
  }
  return String(value)
    .split(/\s+/)
    .filter(Boolean);
}

function parseLiquidArgs(args) {
  const result = {};
  const fileMatch = String(args).trim().match(/^([^\s]+)/);
  if (fileMatch) {
    result.file = fileMatch[1].replace(/^['"]|['"]$/g, "");
  }
  const pattern = /([A-Za-z_][A-Za-z0-9_-]*)\s*=\s*(["'])([\s\S]*?)\2/g;
  let match;
  while ((match = pattern.exec(args)) !== null) {
    result[match[1]] = match[3];
  }
  return result;
}

function loadEmbedCache() {
  if (!fs.existsSync(embedCachePath)) {
    return {};
  }
  return JSON.parse(fs.readFileSync(embedCachePath, "utf8"));
}

function embedKey(url, lang, lines) {
  return `${url} ${lang || "text"} ${lines || ""}`.trim();
}

let mdLib;

module.exports = function (eleventyConfig) {
  const embedCache = loadEmbedCache();

  mdLib = new MarkdownIt({
    html: true,
    linkify: false,
    typographer: false,
    highlight(code, lang) {
      const language = (lang || "").trim();
      if (language && hljs.getLanguage(language)) {
        const highlighted = hljs.highlight(code, { language, ignoreIllegals: true }).value;
        return `<pre><code class="hljs language-${escapeHtml(language)}">${highlighted}</code></pre>`;
      }
      return `<pre><code class="hljs">${escapeHtml(code)}</code></pre>`;
    },
  })
    .use(markdownItAnchor, { permalink: markdownItAnchor.permalink.headerLink() })
    .use(markdownItAttrs)
    .use(markdownItEmoji)
    .use(markdownItFootnote);

  const originalRender = mdLib.render.bind(mdLib);
  mdLib.render = (source, env) => {
    const normalized = String(source)
      .replace(/^\{:\s*\.([A-Za-z0-9_-]+)\s*\}$/gm, "{.$1}")
      .replace(/^\{:\s*start=["']?(\d+)["']?\s*\}$/gm, "{start=$1}")
      .replace(/^<a\s+id=(["'])([^"']+)\1\s*(?:\/>|><\/a>|>)\s*$/gm, '<span id="$2"></span>\n')
      .replace(/^(\[\^[^\]]+]:[^\n]+)\n(?=\[[^\]]+]:)/gm, "$1\n\n")
      .replace(/(^|\n)\$\$\n([\s\S]*?)\n\$\$(?=\n|$)/g, (_match, prefix, math) => {
        return `${prefix}<div class="math-display">$$\n${escapeHtml(math)}\n$$</div>`;
      });
    return originalRender(normalized, env);
  };

  eleventyConfig.setLibrary("md", mdLib);

  eleventyConfig.addPassthroughCopy("assets/images");
  eleventyConfig.addPassthroughCopy("assets/css/style.css");
  eleventyConfig.addPassthroughCopy("img");
  eleventyConfig.addPassthroughCopy("specs");
  eleventyConfig.addPassthroughCopy("CNAME");
  eleventyConfig.addPassthroughCopy("favicon.ico");
  eleventyConfig.addPassthroughCopy("LICENSE.md");
  eleventyConfig.addPassthroughCopy({
    "node_modules/highlight.js/styles/isbl-editor-light.css": "assets/css/highlight-light.css",
    "node_modules/highlight.js/styles/isbl-editor-dark.css": "assets/css/highlight-dark.css",
  });

  eleventyConfig.ignores.add("Gemfile");
  eleventyConfig.ignores.add("Gemfile.lock");
  eleventyConfig.ignores.add("_config.yml");
  eleventyConfig.ignores.add("_plugins/**");
  eleventyConfig.ignores.add("_scripts/**");
  eleventyConfig.ignores.add(".jekyll-cache/**");

  eleventyConfig.addFilter("escape", escapeHtml);
  eleventyConfig.addFilter("xml_escape", escapeXml);
  eleventyConfig.addFilter("relative_url", relativeUrl);
  eleventyConfig.addFilter("absolute_url", absoluteUrl);
  eleventyConfig.addFilter("feed_utm_url", feedUtmUrl);
  eleventyConfig.addFilter("feed_utm_html", feedUtmHtml);
  eleventyConfig.addFilter("canonicalize_internal_urls", canonicalizeInternalHtml);
  eleventyConfig.addFilter("date_to_xmlschema", (date) => new Date(date === "now" ? Date.now() : date).toISOString());
  eleventyConfig.addFilter("date_short", (date) => {
    return new Intl.DateTimeFormat("en", { month: "short", day: "numeric", year: "numeric" }).format(new Date(date));
  });
  eleventyConfig.addFilter("post_url", (post) => postUrlFromData(post.data || post));
  eleventyConfig.addFilter("post_old_url", (post) => postOldUrlFromData(post.data || post));

  eleventyConfig.addCollection("posts", (collectionApi) => {
    return collectionApi
      .getFilteredByGlob("_posts/*.md")
      .sort((a, b) => b.date - a.date);
  });

  eleventyConfig.addGlobalData("eleventyComputed", {
    permalink(data) {
      if (data.permalink) {
        return data.permalink;
      }
      const inputPath = data.page?.inputPath || "";
      if (inputPath.includes("/_posts/") || inputPath.startsWith("./_posts/") || inputPath.startsWith("_posts/")) {
        return postUrlFromData(data);
      }
      if (/^\.\//.test(inputPath)) {
        const relative = inputPath.replace(/^\.\//, "");
        if (/^[^/]+\.(md|html)$/.test(relative)) {
          return rootPageUrl(relative);
        }
      }
      return data.permalink;
    },
    eleventyExcludeFromCollections(data) {
      return Boolean(data.eleventyExcludeFromCollections || data.draft);
    },
  });

  eleventyConfig.addLiquidFilter("escape", escapeHtml);
  eleventyConfig.addLiquidFilter("xml_escape", escapeXml);
  eleventyConfig.addLiquidFilter("relative_url", relativeUrl);
  eleventyConfig.addLiquidFilter("absolute_url", absoluteUrl);
  eleventyConfig.addLiquidFilter("feed_utm_url", feedUtmUrl);
  eleventyConfig.addLiquidFilter("feed_utm_html", feedUtmHtml);
  eleventyConfig.addLiquidFilter("canonicalize_internal_urls", canonicalizeInternalHtml);
  eleventyConfig.addLiquidFilter("date_to_xmlschema", (date) => new Date(date === "now" ? Date.now() : date).toISOString());
  eleventyConfig.addLiquidFilter("date_short", (date) => {
    return new Intl.DateTimeFormat("en", { month: "short", day: "numeric", year: "numeric" }).format(new Date(date));
  });
  eleventyConfig.addLiquidFilter("post_old_url", (post) => postOldUrlFromData(post.data || post));
  eleventyConfig.addLiquidFilter("where_visible", (posts) => (posts || []).filter((post) => post.data.hidden !== true));
  eleventyConfig.addLiquidFilter("list_values", listValues);

  eleventyConfig.addLiquidTag("post_url", function (liquidEngine) {
    return {
      parse(tagToken) {
        this.slug = tagToken.args.trim();
      },
      render() {
        return postMap.byDateSlug.get(this.slug) || "";
      },
    };
  });

  eleventyConfig.addLiquidTag("link", function () {
    return {
      parse(tagToken) {
        this.target = tagToken.args.trim();
      },
      render() {
        return linkUrl(this.target);
      },
    };
  });

  eleventyConfig.addLiquidTag("github_embed", function () {
    return {
      parse(tagToken) {
        const parts = tagToken.args.trim().split(/\s+/);
        this.url = parts[0];
        this.lang = parts[1] || "text";
        this.lines = parts[2] || "";
      },
      render() {
        const key = embedKey(this.url, this.lang, this.lines);
        const entry = embedCache[key];
        if (!entry) {
          throw new Error(`Missing cached GitHub embed: ${key}. Run npm run refresh-embeds.`);
        }
        return `\n\`\`\`${this.lang}\n${entry.code.replace(/\n$/, "")}\n\`\`\`\n`;
      },
    };
  });

  eleventyConfig.addLiquidTag("include", function () {
    return {
      parse(tagToken) {
        this.args = parseLiquidArgs(tagToken.args);
      },
      render() {
        const file = this.args.file;
        if (file === "webp.html") {
          const src = this.args.src || "";
          const alt = this.args.alt || "";
          const webp = src.replace(/\.(jpg|png)$/i, ".webp");
          return `<picture>
  <source srcset="/img/${escapeHtml(webp)}" type="image/webp">
  <img class="responsive-img" src="/img/${escapeHtml(src)}" alt="${escapeHtml(alt)}">
</picture>`;
        }
        if (file === "youtube.html") {
          const id = this.args.id || "";
          return `<div class="embed-container"><iframe width="640" height="390" src="https://www.youtube.com/embed/${escapeHtml(id)}" frameborder="0" allowfullscreen></iframe></div>`;
        }
        if (file === "tip.html") {
          const content = mdLib.render(this.args.content || "");
          return `<div class="tip-box">
  <div class="tip-header"><strong>Tip:</strong></div>
  <div class="tip">${content}</div>
</div>`;
        }
        throw new Error(`Unsupported include: ${file}`);
      },
    };
  });

  return {
    dir: {
      input: ".",
      output: outputDir,
      includes: "_includes",
      layouts: "_layouts",
      data: "_data",
    },
    markdownTemplateEngine: "liquid",
    htmlTemplateEngine: "liquid",
    dataTemplateEngine: "liquid",
    templateFormats: ["md", "html", "liquid", "xml"],
  };
};
