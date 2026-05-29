# frozen_string_literal: true

require "cgi"
require "uri"

module Jekyll
  module FeedUtm
    UTM_PARAMS = {
      "utm_source" => "protocols_made_fun",
      "utm_medium" => "feed",
      "utm_campaign" => "pmf_feed"
    }.freeze

    SKIP_SCHEMES = %w[mailto javascript tel data].freeze

    def feed_utm_url(input, base_url = nil)
      original = input.to_s
      raw = CGI.unescapeHTML(original.strip)
      return original if raw.empty?

      uri = parse_feed_url(raw, base_url)
      return original unless uri

      params = URI.decode_www_form(uri.query.to_s)
      keys = params.map(&:first)
      UTM_PARAMS.each do |key, value|
        params << [key, value] unless keys.include?(key)
      end
      uri.query = URI.encode_www_form(params)
      uri.to_s
    rescue URI::InvalidURIError
      original
    end

    def feed_utm_html(input, base_url = nil)
      input.to_s.gsub(/(\b(?:href|src)\s*=\s*)(["'])(.*?)\2/i) do
        prefix = Regexp.last_match(1)
        quote = Regexp.last_match(2)
        url = Regexp.last_match(3)
        tagged = feed_utm_url(url, base_url)
        "#{prefix}#{quote}#{CGI.escapeHTML(tagged)}#{quote}"
      end
    end

    private

    def parse_feed_url(raw, base_url)
      uri = URI.parse(raw)
      return nil if uri.scheme && SKIP_SCHEMES.include?(uri.scheme.downcase)
      return uri if uri.is_a?(URI::HTTP) || uri.is_a?(URI::HTTPS)

      base = base_url.to_s.empty? ? site_base_url : base_url.to_s
      return nil if base.empty?

      URI.join(base, raw)
    end

    def site_base_url
      site = @context.registers[:site]
      site.config["url"].to_s
    end
  end
end

Liquid::Template.register_filter(Jekyll::FeedUtm)
